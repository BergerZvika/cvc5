/******************************************************************************
 * Top contributors (to current version):
 *   Zvika Berger
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 */

#include "preprocessing/passes/exp_analyzer.h"

#include <algorithm>
#include <functional>
#include <iostream>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "expr/node.h"
#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/passes/int_order_facts.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "util/integer.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

namespace {

// If `n` is an EXP integer power, set `base`/`exp` to its base and exponent
// and return true. Only EXP (binary, base^exp) is handled.
bool asPower(TNode n, Node& base, TNode& exp)
{
  if (n.getKind() != Kind::EXP) return false;
  base = n[0];
  exp = n[1];
  return true;
}

// Walk n recursively (no visited set) and accumulate, for each power
// subterm, its tree-occurrence count.
void collectExpCounts(TNode n,
                      std::map<Node, uint64_t>& counts,
                      std::vector<Node>& order)
{
  Node base;
  TNode exp;
  if (asPower(n, base, exp))
  {
    auto [it, inserted] = counts.emplace(n, 0);
    if (inserted) order.push_back(n);
    it->second++;
  }
  for (TNode c : n) collectExpCounts(c, counts, order);
}

// Linearly accumulate `e` (scaled by -1 when `neg`) into `offset` (the
// integer-constant part) and `terms` (the signed non-constant atoms),
// recursing through ADD/SUB/NEG. We do NOT assume the rewriter has
// eliminated subtraction/negation: (- a b), (- a) and nested mixes are all
// handled, so `X-c`, `c-X` and `-(X)+c` decompose just like `X+c`.
void accumExp(TNode e,
              bool neg,
              Rational& offset,
              std::vector<std::pair<Node, bool>>& terms)
{
  if (e.isConst())
  {
    const Rational& r = e.getConst<Rational>();
    if (r.isIntegral())
    {
      offset += neg ? -r : r;
      return;
    }
    terms.push_back({e, neg});  // non-integral const: keep as an atom
    return;
  }
  switch (e.getKind())
  {
    case Kind::ADD:
      for (TNode c : e) accumExp(c, neg, offset, terms);
      return;
    case Kind::SUB:  // binary: e[0] - e[1]
      accumExp(e[0], neg, offset, terms);
      accumExp(e[1], !neg, offset, terms);
      return;
    case Kind::NEG:  // unary: -e[0]
      accumExp(e[0], !neg, offset, terms);
      return;
    default: terms.push_back({e, neg}); return;  // opaque atom
  }
}

// Decompose an EXP exponent `e` into (symbolic, offset) such that
// e == symbolic + offset, where `offset` is e's integer-constant part and
// `symbolic` is a canonical (sorted) sum of the remaining signed atoms. Two
// exponents sharing the same `symbolic` differ only by a constant, so for a
// fixed base c the powers are related by c^(S+a) = c^|a-b| * c^(S+b).
//
// The returned `symbolic` node is only ever used as a grouping key (never
// inserted into the assertions), so a rebuilt/sorted node is fine here.
Node splitExp(TNode e, Rational& offset)
{
  offset = Rational(0);
  std::vector<std::pair<Node, bool>> terms;  // (atom, negated?)
  accumExp(e, false, offset, terms);
  if (terms.empty())
  {
    // Fully constant exponent (shouldn't normally survive rewriting).
    offset = Rational(0);
    return e;
  }
  if (terms.size() == 1 && !terms[0].second) return terms[0].first;
  // Canonicalize so equal symbolic parts collide regardless of term order.
  std::sort(terms.begin(),
            terms.end(),
            [](const std::pair<Node, bool>& a,
               const std::pair<Node, bool>& b) {
              if (a.first != b.first) return a.first < b.first;
              return a.second < b.second;
            });
  NodeManager* nm = e.getNodeManager();
  std::vector<Node> parts;
  for (const auto& [atom, an] : terms)
  {
    parts.push_back(an ? nm->mkNode(Kind::NEG, atom) : Node(atom));
  }
  return parts.size() == 1 ? parts[0] : nm->mkNode(Kind::ADD, parts);
}

// DAG-walk substitution: replace nodes per `sub` map.
Node subst(TNode n,
           std::unordered_map<TNode, Node>& cache,
           const std::unordered_map<Node, Node>& sub)
{
  auto cit = cache.find(n);
  if (cit != cache.end()) return cit->second;
  auto sit = sub.find(n);
  if (sit != sub.end())
  {
    cache[n] = sit->second;
    return sit->second;
  }
  if (n.getNumChildren() == 0)
  {
    cache[n] = n;
    return n;
  }
  NodeBuilder nb(n.getNodeManager(), n.getKind());
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    nb << n.getOperator();
  }
  bool changed = false;
  for (TNode c : n)
  {
    Node nc = subst(c, cache, sub);
    if (nc != c) changed = true;
    nb << nc;
  }
  Node result = changed ? Node(nb) : Node(n);
  cache[n] = result;
  return result;
}

}  // namespace

ExpAnalyzer::ExpAnalyzer(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "exp-analyzer")
{
}

PreprocessingPassResult ExpAnalyzer::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  using Mode = options::AnalyzeExpInstancesMode;
  Mode mode = options().smt.analyzeExpInstances;
  if (mode == Mode::NONE) return PreprocessingPassResult::NO_CONFLICT;

  const bool report = mode == Mode::MULTIPLY_ONLY_REPORT
                      || mode == Mode::COMMON_REPORT
                      || mode == Mode::MULTIPLY_ONLY_L3_REPORT
                      || mode == Mode::MULTIPLY_ONLY_L3_COMMON_REPORT
                      || mode == Mode::MULTIPLY_ONLY_L3_COMMON_L4_REPORT
                      || mode == Mode::MULTIPLY_ONLY_L4_REPORT
                      || mode == Mode::MULTIPLY_ONLY_RELATE_REPORT;
  // After the multiply-only merge, optionally relate the powers it could not
  // fold (those whose exponent gap is symbolic). L3 and L4 are selectable
  // independently so their contributions can be measured apart.
  // l3-common: one factorization per upper power, pivoting on the most
  // frequent lower power (see addRelationalLemmas). Under l3-common, L4 is
  // emitted only for that same chosen pair, so it introduces no power term
  // beyond the b^(y-x) that L3 already adds.
  const bool l3Common = mode == Mode::MULTIPLY_ONLY_L3_COMMON
                        || mode == Mode::MULTIPLY_ONLY_L3_COMMON_REPORT
                        || mode == Mode::MULTIPLY_ONLY_L3_COMMON_L4
                        || mode == Mode::MULTIPLY_ONLY_L3_COMMON_L4_REPORT;
  const bool doL3 = mode == Mode::MULTIPLY_ONLY_L3
                    || mode == Mode::MULTIPLY_ONLY_L3_REPORT
                    || l3Common
                    || mode == Mode::MULTIPLY_ONLY_RELATE
                    || mode == Mode::MULTIPLY_ONLY_RELATE_REPORT;
  const bool doL4 = mode == Mode::MULTIPLY_ONLY_L4
                    || mode == Mode::MULTIPLY_ONLY_L4_REPORT
                    || mode == Mode::MULTIPLY_ONLY_L3_COMMON_L4
                    || mode == Mode::MULTIPLY_ONLY_L3_COMMON_L4_REPORT
                    || mode == Mode::MULTIPLY_ONLY_RELATE
                    || mode == Mode::MULTIPLY_ONLY_RELATE_REPORT;
  const bool relate = doL3 || doL4 || l3Common;
  // commonPivot: pivot on the most-frequent instance and divide smaller
  // powers down (naive scheme). Otherwise pivot on the smallest exponent and
  // only multiply up (exact).
  const bool commonPivot =
      mode == Mode::COMMON || mode == Mode::COMMON_REPORT;

  std::map<Node, uint64_t> counts;
  std::vector<Node> order;
  for (size_t i = 0, sz = assertionsToPreprocess->size(); i < sz; ++i)
  {
    collectExpCounts((*assertionsToPreprocess)[i], counts, order);
  }

  uint64_t total = 0;
  for (auto& [_, c] : counts) total += c;

  if (report)
  {
    std::cout << ";; EXP-analyzer ----------------------------------------\n";
    std::cout << ";; distinct instances: " << counts.size() << "\n";
    std::cout << ";; total occurrences:  " << total << "\n";
    for (size_t id = 0; id < order.size(); ++id)
    {
      const Node& n = order[id];
      Node b;
      TNode ex;
      asPower(n, b, ex);  // always true: order holds only power nodes
      std::cout << ";; #" << id
                << "\tcount=" << counts[n]
                << "\tbase=" << b
                << "\texp=" << ex
                << "\tnode=" << n << "\n";
    }
  }

  // Group EXP instances by (base, symbolic exponent part). Within each group
  // the base b is fixed and every exponent is (S + const) for the same S, so
  // all instances are related by b^(S+a) = b^(a-p) * b^(S+p) for the pivot
  // offset p. Pivoting on the SMALLEST offset makes every a-p >= 0, so the
  // factor b^(a-p) is always a non-negative power and every member rewrites
  // via MULT (never division). The base may be:
  //   * an integer constant c (any sign): factor is the constant c^(a-p);
  //   * a symbolic term: factor is b^(a-p) built as a product of (a-p) copies
  //     of b (capped to keep the product small).
  // A non-integral constant base is skipped (no exact integer factor).
  NodeManager* nm = nodeManager();

  struct Member
  {
    Node node;
    Rational off;
  };
  // key = (base b, symbolic exponent S). Insertion order of each vector
  // follows `order`, so ties below break deterministically by first
  // appearance.
  std::map<std::pair<Node, Node>, std::vector<Member>> groups;
  for (const Node& n : order)
  {
    Node base;
    TNode exp;
    asPower(n, base, exp);  // always true: order holds only power nodes
    // Skip only bases we cannot form an exact integer factor for: a
    // non-integral constant base. Constant integers (incl. negative) and
    // symbolic bases are both kept.
    if (base.isConst() && !base.getConst<Rational>().isIntegral()) continue;
    Rational off;
    Node sym = splitExp(exp, off);
    groups[{base, sym}].push_back({n, off});
  }

  // Cap on the product length b*b*...*b used for a symbolic base, so a large
  // exponent gap cannot blow the term up. Constant bases have no such limit
  // (their factor is a single constant c^d) beyond the sanity bound below.
  const Integer kMaxSymChain(256);
  std::unordered_map<Node, Node> sub;  // node-to-replace -> replacement
  for (auto& [key, members] : groups)
  {
    if (members.size() < 2) continue;
    const Node& base = key.first;
    const bool constBase = base.isConst();
    // Pivot choice (see commonPivot above):
    //  * default: the member with the SMALLEST exponent offset (ties -> most
    //    occurrences). Every other member is then a LARGER power reached by
    //    MULT only -- never pivot div b^d. That matters for solving: the
    //    division form b^n div b loses the divisibility fact b | b^n, so an
    //    identity like b*(b^n div b) = b^n never closes and the solver
    //    diverges. Multiplying up keeps the rewrite exact.
    //  * commonPivot: the member with the MOST occurrences (ties -> smallest
    //    offset). Smaller powers are then rewritten by DIVIDING the pivot
    //    down. Kept for A/B comparison against the default.
    size_t piv = 0;
    for (size_t i = 1; i < members.size(); ++i)
    {
      const uint64_t ci = counts[members[i].node];
      const uint64_t cp = counts[members[piv].node];
      bool better;
      if (commonPivot)
      {
        better = ci > cp || (ci == cp && members[i].off < members[piv].off);
      }
      else
      {
        better = members[i].off < members[piv].off
                 || (members[i].off == members[piv].off && ci > cp);
      }
      if (better) piv = i;
    }
    const Node& pivot = members[piv].node;
    const Rational& pOff = members[piv].off;
    for (size_t i = 0; i < members.size(); ++i)
    {
      if (i == piv) continue;
      const Node& m = members[i].node;
      Rational d = members[i].off - pOff;  // exponent(m) - exponent(pivot)
      if (d.isZero()) continue;            // identical exponent value
      // In the default (smallest) pivot mode d > 0 always; with commonPivot d
      // may be negative (smaller power -> divide down).
      Assert(commonPivot || d.sgn() > 0);
      Integer ad = d.getNumerator().abs();
      // Build the factor b^|d| (a constant for a constant base, a product of
      // |d| copies for a symbolic base, so the rewrite stays in-theory).
      Node factor;
      if (constBase)
      {
        // Skip absurd exponents (keeps the c^|d| constant sane).
        if (ad > Integer(1000000)) continue;
        Integer cBase = base.getConst<Rational>().getNumerator();
        factor = nm->mkConstInt(Rational(cBase.pow(ad.toUnsignedInt())));
      }
      else
      {
        // Skip if |d| is too large to expand into a product.
        if (ad > kMaxSymChain) continue;
        uint32_t dd = ad.toUnsignedInt();
        std::vector<Node> copies(dd, base);
        factor = dd == 1 ? base : nm->mkNode(Kind::MULT, copies);
      }
      if (d.sgn() > 0)
      {
        // m is the larger power: b^(S+a) = b^|d| * b^(S+p)
        sub[m] = nm->mkNode(Kind::MULT, factor, pivot);
      }
      else
      {
        // m is the smaller power: b^(S+a) = b^(S+p) div b^|d|
        sub[m] = nm->mkNode(Kind::INTS_DIVISION_TOTAL, pivot, factor);
      }
    }
  }

  if (report)
  {
    std::cout << ";; rewrite pairs: " << sub.size() << "\n";
    for (const auto& [from, to] : sub)
    {
      std::cout << ";;   " << from << "  ==>  " << to << "\n";
    }
    std::cout << ";; -----------------------------------------------------\n";
  }

  if (!sub.empty())
  {
    std::unordered_map<TNode, Node> cache;
    for (size_t i = 0, sz = assertionsToPreprocess->size(); i < sz; ++i)
    {
      Node before = (*assertionsToPreprocess)[i];
      Node after = subst(before, cache, sub);
      if (after != before) assertionsToPreprocess->replace(i, after);
    }
  }

  if (relate)
  {
    addRelationalLemmas(assertionsToPreprocess, report, doL3, doL4, l3Common);
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

// ---------------------------------------------------------------------------
// Relational lemmas for the powers multiply-only could not merge.
//
// multiply-only folds two same-base powers only when their exponent gap is a
// CONSTANT: b^(S+a) becomes b^|a-p| * b^(S+p).  When the gap is symbolic --
// b^x and b^y with y-x not a numeral -- it can do nothing, and the arithmetic
// solver then treats the two powers as unrelated variables even when the
// assertions plainly order the exponents.  This adds that link back, for an
// arbitrary base rather than only base 2:
//
//   L3  b^y = b^x * b^(y-x)      when x <= y   (gives divisibility b^x | b^y)
//   L4  b^y >= b * b^x           when x <  y   and b >= 2
//
// L3 is also accompanied by b^(y-x) >= 1 (and >= b under L4's conditions),
// since it introduces that term.
//
// WHEN a lemma is emitted -- every condition must be ENTAILED by the
// assertions (via IntOrderFacts), so each lemma is implied by the input and
// satisfiability cannot change:
//   * both powers occur in the assertions and share a syntactically equal base;
//   * the base is an integer >= 1 (L3) or >= 2 (L4): checked directly for a
//     numeral, otherwise entailed;
//   * both exponents are entailed non-negative (integer power semantics);
//   * x <= y (L3) / x < y (L4) is entailed;
//   * the gap y-x is NOT a constant -- those pairs multiply-only already
//     merged exactly, and re-relating them only duplicates terms;
//   * neither power sits under a quantifier.
// Lemmas are rewritten, dropped if constant-true, and deduplicated.  The pair
// loop is capped to keep it quadratic in a small number of instances.
// ---------------------------------------------------------------------------
void ExpAnalyzer::addRelationalLemmas(AssertionPipeline* assertionsToPreprocess,
                                      bool report,
                                      bool doL3,
                                      bool doL4,
                                      bool l3Common)
{
  NodeManager* nm = nodeManager();

  std::vector<Node> cur;
  cur.reserve(assertionsToPreprocess->size());
  for (size_t i = 0, sz = assertionsToPreprocess->size(); i < sz; ++i)
  {
    cur.push_back((*assertionsToPreprocess)[i]);
  }

  // Collect the surviving powers, skipping quantifier bodies.
  std::vector<Node> powers;
  std::unordered_set<Node> pseen;
  std::function<void(TNode)> collect = [&](TNode n) {
    if (!pseen.insert(n).second || n.isClosure()) return;
    if (n.getKind() == Kind::EXP) powers.push_back(n);
    for (TNode c : n) collect(c);
  };
  for (const Node& a : cur) collect(a);

  const size_t kMaxInstances = 48;
  if (powers.size() < 2 || powers.size() > kMaxInstances)
  {
    return;
  }

  IntOrderFacts facts(d_preprocContext->getEnv());
  facts.harvest(cur);

  const Rational one(1);
  const Rational two(2);
  Node onen = nm->mkConstInt(one);

  std::vector<Node> lemmas;
  std::unordered_set<Node> emitted;
  auto add = [&](Node lem) {
    Node r = rewrite(lem);
    if (r.isConst()) return;  // already trivially true
    if (!emitted.insert(r).second) return;
    lemmas.push_back(r);
  };

  // Is the base a usable integer >= bound?
  auto baseAtLeast = [&](TNode b, const Rational& bound) {
    if (!b.getType().isInteger()) return false;
    if (b.isConst())
    {
      const Rational& v = b.getConst<Rational>();
      return v.isIntegral() && v >= bound;
    }
    return facts.geqConst(b, bound);
  };

  // Occurrence counts, so the l3-common mode can pivot on the most frequent
  // lower power instead of relating every ordered pair.
  std::map<Node, uint64_t> occ;
  {
    std::vector<Node> order2;
    for (const Node& a : cur) collectExpCounts(a, occ, order2);
  }

  // Does (px, py) qualify for a relational lemma?  All conditions must be
  // entailed by the assertions, so any lemma emitted is implied by the input.
  auto qualifies = [&](const Node& px, const Node& py, Node& gapOut) {
    if (px == py || px[0] != py[0]) return false;
    if (!facts.nonNeg(px[1]) || !facts.nonNeg(py[1])) return false;
    if (!facts.leq(px[1], py[1])) return false;
    Node gap = rewrite(nm->mkNode(Kind::SUB, py[1], px[1]));
    if (gap.isConst()) return false;  // multiply-only already folds these
    if (!baseAtLeast(px[0], one)) return false;
    gapOut = gap;
    return true;
  };

  auto emitL3 = [&](const Node& px, const Node& py, const Node& gap) {
    Node pgap = nm->mkNode(Kind::EXP, px[0], gap);
    add(nm->mkNode(Kind::EQUAL, py, nm->mkNode(Kind::MULT, px, pgap)));
    add(nm->mkNode(Kind::GEQ, pgap, onen));
  };

  // L4: strict monotonicity, needs a strictly ordered exponent pair and a
  // genuinely growing base.  Both extra conditions are checked here, so the
  // caller can offer any qualifying pair and the lemma is simply skipped when
  // they do not hold.
  auto emitL4 = [&](const Node& px, const Node& py, const Node& gap) {
    if (!facts.lt(px[1], py[1]) || !baseAtLeast(px[0], two)) return;
    Node pgap = nm->mkNode(Kind::EXP, px[0], gap);
    add(nm->mkNode(Kind::GEQ, py, nm->mkNode(Kind::MULT, px[0], px)));
    add(nm->mkNode(Kind::GEQ, pgap, px[0]));
  };

  if (l3Common)
  {
    // One lemma per UPPER power: relate it to the single most frequently
    // occurring lower power, rather than to every lower power.  This caps the
    // number of introduced b^(y-x) terms at one per upper power instead of one
    // per ordered pair.  Ties break on the smaller exponent, then on node id,
    // so the choice is deterministic.
    for (const Node& py : powers)
    {
      const Node* best = nullptr;
      Node bestGap;
      uint64_t bestCount = 0;
      for (const Node& px : powers)
      {
        Node gap;
        if (!qualifies(px, py, gap)) continue;
        uint64_t c = occ.count(px) ? occ[px] : 0;
        bool better;
        if (best == nullptr)
        {
          better = true;
        }
        else if (c != bestCount)
        {
          better = c > bestCount;
        }
        else if (facts.leq(px[1], (*best)[1]) != facts.leq((*best)[1], px[1]))
        {
          better = facts.leq(px[1], (*best)[1]);
        }
        else
        {
          better = px < *best;
        }
        if (better)
        {
          best = &px;
          bestGap = gap;
          bestCount = c;
        }
      }
      if (best != nullptr)
      {
        emitL3(*best, py, bestGap);
        // l3-common-l4: L4 for the SAME pair L3 just picked, so it reuses the
        // b^(y-x) term L3 introduced and adds no further power term.
        if (doL4)
        {
          emitL4(*best, py, bestGap);
        }
      }
    }
  }
  else
  {
    for (const Node& px : powers)
    {
      for (const Node& py : powers)
      {
        Node gap;
        if (!qualifies(px, py, gap)) continue;
        if (doL3)
        {
          emitL3(px, py, gap);
        }
        if (doL4)
        {
          emitL4(px, py, gap);
        }
      }
    }
  }

  if (report)
  {
    std::cout << ";; relational lemmas: " << lemmas.size() << "\n";
    for (const Node& l : lemmas) std::cout << ";;   " << l << "\n";
    std::cout << ";; -----------------------------------------------------\n";
  }
  for (const Node& l : lemmas)
  {
    assertionsToPreprocess->push_back(l);
  }
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
