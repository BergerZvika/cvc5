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

  const bool report = mode == Mode::REWRITE_REPORT;

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

  // Group constant-base EXP instances by (base, symbolic exponent part).
  // Within each group the base c is fixed
  // and every exponent is (S + const) for the same S, so all instances are
  // constant-factor related via c^(S+a) = c^|a-b| * c^(S+b), and can be
  // translated to a single representative: the instance with the most
  // occurrences. Larger powers translate via MULT, smaller ones via DIV
  // (exact, since c^|d| divides).
  NodeManager* nm = nodeManager();

  struct Member
  {
    Node node;
    Rational off;
  };
  // key = (constant base c, symbolic exponent S). Insertion order of each
  // vector follows `order`, so ties below break deterministically by first
  // appearance.
  std::map<std::pair<Node, Node>, std::vector<Member>> groups;
  for (const Node& n : order)
  {
    Node base;
    TNode exp;
    asPower(n, base, exp);  // always true: order holds only power nodes
    if (!base.isConst()) continue;
    const Rational& c = base.getConst<Rational>();
    if (!c.isIntegral() || c < Rational(2)) continue;  // need integer c >= 2
    Rational off;
    Node sym = splitExp(exp, off);
    groups[{base, sym}].push_back({n, off});
  }

  std::unordered_map<Node, Node> sub;  // node-to-replace -> replacement
  for (auto& [key, members] : groups)
  {
    if (members.size() < 2) continue;
    // c is integral and >= 2 (filtered above).
    Integer cBase = key.first.getConst<Rational>().getNumerator();
    // Pivot = the member with the most occurrences.
    size_t piv = 0;
    for (size_t i = 1; i < members.size(); ++i)
    {
      if (counts[members[i].node] > counts[members[piv].node]) piv = i;
    }
    const Node& pivot = members[piv].node;
    const Rational& pOff = members[piv].off;
    for (size_t i = 0; i < members.size(); ++i)
    {
      if (i == piv) continue;
      const Node& m = members[i].node;
      Rational d = members[i].off - pOff;  // exponent(m) - exponent(pivot)
      if (d.isZero()) continue;            // identical exponent value
      Integer ad = d.getNumerator().abs();
      // Skip absurd exponents (keeps the c^|d| constant sane).
      if (ad > Integer(1000000)) continue;
      Node factor = nm->mkConstInt(Rational(cBase.pow(ad.toUnsignedInt())));
      if (d.sgn() > 0)
      {
        // m is the larger power: c^(S+a) = c^|d| * c^(S+p)
        sub[m] = nm->mkNode(Kind::MULT, factor, pivot);
      }
      else
      {
        // m is the smaller power: c^(S+a) = c^(S+p) div c^|d|
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

  if (sub.empty()) return PreprocessingPassResult::NO_CONFLICT;

  std::unordered_map<TNode, Node> cache;
  for (size_t i = 0, sz = assertionsToPreprocess->size(); i < sz; ++i)
  {
    Node before = (*assertionsToPreprocess)[i];
    Node after = subst(before, cache, sub);
    if (after != before) assertionsToPreprocess->replace(i, after);
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
