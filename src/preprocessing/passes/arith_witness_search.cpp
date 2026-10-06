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
 *
 * Implementation of the arith-witness-search preprocessing pass.
 */

#include "preprocessing/passes/arith_witness_search.h"

#include <algorithm>
#include <unordered_set>
#include <vector>

#include "expr/node_algorithm.h"
#include "options/arith_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/rewriter.h"
#include "util/rational.h"
#include "util/statistics_registry.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

namespace {

/** Values wider than this are treated as out of range; keeps x^9 in check. */
const size_t s_maxBits = 4096;
/** Largest constant exponent expanded by repeated multiplication. */
const uint32_t s_maxExp = 64;

/** Euclidean quotient, matching INTS_DIVISION_TOTAL (division by 0 is 0). */
Integer eDiv(const Integer& a, const Integer& b)
{
  if (b.sgn() == 0)
  {
    return Integer(0);
  }
  return a.euclidianDivideQuotient(b);
}

bool tooBig(const Integer& i) { return i.length() > s_maxBits; }

/** Flatten top-level conjunctions. */
void collectConjuncts(TNode n, std::vector<Node>& out)
{
  if (n.getKind() == Kind::AND)
  {
    for (const Node& c : n)
    {
      collectConjuncts(c, out);
    }
    return;
  }
  out.push_back(n);
}

/** Free integer variables. */
void collectVars(TNode n,
                 std::unordered_set<Node>& vs,
                 std::unordered_set<TNode>& visited)
{
  if (!visited.insert(n).second)
  {
    return;
  }
  if (n.isVar() && n.getKind() != Kind::BOUND_VARIABLE
      && n.getType().isInteger())
  {
    vs.insert(n);
    return;
  }
  for (const Node& c : n)
  {
    collectVars(c, vs, visited);
  }
}

/** Deterministic xorshift, so a run is reproducible. */
uint64_t nextRand(uint64_t& s)
{
  s ^= s << 13;
  s ^= s >> 7;
  s ^= s << 17;
  return s;
}

}  // namespace

ArithWitnessSearch::ArithWitnessSearch(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "arith-witness-search"),
      d_stats(statisticsRegistry())
{
}

ArithWitnessSearch::Statistics::Statistics(StatisticsRegistry& reg)
    : d_numSolved(
        reg.registerInt("preprocessing::passes::ArithWitnessSearch::NumSolved")),
      d_numFailed(
          reg.registerInt("preprocessing::passes::ArithWitnessSearch::NumFailed")),
      d_numSteps(
          reg.registerInt("preprocessing::passes::ArithWitnessSearch::NumSteps")),
      d_numSkipped(reg.registerInt(
          "preprocessing::passes::ArithWitnessSearch::NumSkipped")),
      d_numEnumSolved(reg.registerInt(
          "preprocessing::passes::ArithWitnessSearch::NumEnumSolved"))
{
}

bool ArithWitnessSearch::evalTerm(TNode n,
                                 const Assign& a,
                                 Cache& ca,
                                 Integer& out) const
{
  Cache::const_iterator cit = ca.find(n);
  if (cit != ca.end())
  {
    out = cit->second;
    return true;
  }
  if (!evalTermRec(n, a, ca, out))
  {
    return false;
  }
  ca[n] = out;
  return true;
}

bool ArithWitnessSearch::evalTermRec(TNode n,
                                     const Assign& a,
                                     Cache& ca,
                                     Integer& out) const
{
  if (n.isConst())
  {
    Kind ck = n.getKind();
    if (ck != Kind::CONST_INTEGER && ck != Kind::CONST_RATIONAL)
    {
      return false;
    }
    const Rational& r = n.getConst<Rational>();
    if (!r.isIntegral())
    {
      return false;
    }
    out = r.getNumerator();
    return true;
  }
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::ADD:
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
    {
      Integer acc = (k == Kind::ADD) ? Integer(0) : Integer(1);
      for (const Node& c : n)
      {
        Integer v;
        if (!evalTerm(c, a, ca, v))
        {
          return false;
        }
        acc = (k == Kind::ADD) ? acc + v : acc * v;
        if (tooBig(acc))
        {
          return false;
        }
      }
      out = acc;
      return true;
    }
    case Kind::SUB:
    {
      Integer x, y;
      if (!evalTerm(n[0], a, ca, x) || !evalTerm(n[1], a, ca, y))
      {
        return false;
      }
      out = x - y;
      return !tooBig(out);
    }
    case Kind::NEG:
    {
      Integer x;
      if (!evalTerm(n[0], a, ca, x))
      {
        return false;
      }
      out = -x;
      return true;
    }
    case Kind::POW:
    case Kind::EXP:
    {
      Integer b, e;
      if (!evalTerm(n[0], a, ca, b) || !evalTerm(n[1], a, ca, e))
      {
        return false;
      }
      if (e.sgn() >= 0)
      {
        if (!e.fitsUnsignedInt() || e > Integer(s_maxExp))
        {
          return false;
        }
        // guard the RESULT size before computing it
        if (b.abs() > Integer(1) && b.length() * e.toUnsignedInt() > s_maxBits)
        {
          return false;
        }
        out = b.pow(e.toUnsignedInt());
        return !tooBig(out);
      }
      // Negative exponent under this solver's '**': exp(s,t) = 1 div s^|t|,
      // which is 0 for |s| > 1 and for s = 0, and +-1 for s = +-1.
      Integer ae = -e;
      if (!ae.fitsUnsignedInt() || ae > Integer(s_maxExp))
      {
        return false;
      }
      if (b.abs() > Integer(1))
      {
        out = Integer(0);
        return true;
      }
      Integer q = b.pow(ae.toUnsignedInt());
      out = eDiv(Integer(1), q);
      return true;
    }
    case Kind::INTS_DIVISION:
    case Kind::INTS_DIVISION_TOTAL:
    {
      Integer x, y;
      if (!evalTerm(n[0], a, ca, x) || !evalTerm(n[1], a, ca, y))
      {
        return false;
      }
      out = eDiv(x, y);
      return true;
    }
    case Kind::INTS_MODULUS:
    case Kind::INTS_MODULUS_TOTAL:
    {
      Integer x, y;
      if (!evalTerm(n[0], a, ca, x) || !evalTerm(n[1], a, ca, y))
      {
        return false;
      }
      out = (y.sgn() == 0) ? x : x - eDiv(x, y) * y;
      return true;
    }
    default: break;
  }
  if (n.isVar() && n.getType().isInteger())
  {
    Assign::const_iterator it = a.find(n);
    if (it == a.end())
    {
      return false;
    }
    out = it->second;
    return true;
  }
  return false;
}

bool ArithWitnessSearch::evalPenalty(TNode c,
                                     const Assign& a,
                                     Cache& ca,
                                     Integer& pen) const
{
  Kind k = c.getKind();
  if (k == Kind::CONST_BOOLEAN)
  {
    pen = c.getConst<bool>() ? Integer(0) : Integer(1);
    return true;
  }
  if (k == Kind::NOT)
  {
    Integer sub;
    if (!evalPenalty(c[0], a, ca, sub))
    {
      return false;
    }
    pen = (sub.sgn() == 0) ? Integer(1) : Integer(0);
    return true;
  }
  if (k == Kind::IMPLIES)
  {
    Integer x, y;
    if (!evalPenalty(c[0], a, ca, x) || !evalPenalty(c[1], a, ca, y))
    {
      return false;
    }
    pen = (x.sgn() != 0 || y.sgn() == 0) ? Integer(0) : y;
    return true;
  }
  if (k == Kind::ITE && c.getNumChildren() == 3 && c.getType().isBoolean())
  {
    Integer cond;
    if (!evalPenalty(c[0], a, ca, cond))
    {
      return false;
    }
    return evalPenalty(cond.sgn() == 0 ? c[1] : c[2], a, ca, pen);
  }
  if (k == Kind::XOR)
  {
    Integer x, y;
    if (!evalPenalty(c[0], a, ca, x) || !evalPenalty(c[1], a, ca, y))
    {
      return false;
    }
    pen = ((x.sgn() == 0) != (y.sgn() == 0)) ? Integer(0) : Integer(1);
    return true;
  }
  if (k == Kind::EQUAL && c.getNumChildren() == 2 && c[0].getType().isBoolean())
  {
    Integer x, y;
    if (!evalPenalty(c[0], a, ca, x) || !evalPenalty(c[1], a, ca, y))
    {
      return false;
    }
    pen = ((x.sgn() == 0) == (y.sgn() == 0)) ? Integer(0) : Integer(1);
    return true;
  }
  if (k == Kind::AND || k == Kind::OR)
  {
    Integer acc = (k == Kind::AND) ? Integer(0) : Integer(-1);
    for (const Node& ch : c)
    {
      Integer sub;
      if (!evalPenalty(ch, a, ca, sub))
      {
        return false;
      }
      if (k == Kind::AND)
      {
        acc = acc + sub;
      }
      else if (acc.sgn() < 0 || sub < acc)
      {
        acc = sub;  // OR: the cheapest disjunct to repair
      }
    }
    pen = acc.sgn() < 0 ? Integer(0) : acc;
    return true;
  }
  if ((k == Kind::EQUAL || k == Kind::GEQ || k == Kind::GT || k == Kind::LEQ
       || k == Kind::LT)
      && c.getNumChildren() == 2 && c[0].getType().isInteger())
  {
    Integer x, y;
    if (!evalTerm(c[0], a, ca, x) || !evalTerm(c[1], a, ca, y))
    {
      return false;
    }
    // A graded penalty, so that an unsatisfied inequality tells the search
    // WHICH WAY to move its roots rather than merely that it is unsatisfied.
    Integer d = x - y;
    switch (k)
    {
      case Kind::EQUAL: pen = d.abs(); break;
      case Kind::GEQ: pen = d.sgn() >= 0 ? Integer(0) : -d; break;
      case Kind::GT: pen = d.sgn() > 0 ? Integer(0) : Integer(1) - d; break;
      case Kind::LEQ: pen = d.sgn() <= 0 ? Integer(0) : d; break;
      default: pen = d.sgn() < 0 ? Integer(0) : Integer(1) + d; break;
    }
    return true;
  }
  return false;
}

void ArithWitnessSearch::propagate(const Problem& p, Assign& a) const
{
  bool prog = true;
  size_t rounds = 0;
  while (prog && rounds++ < 200)
  {
    prog = false;
    for (size_t ei : p.d_eqs)
    {
      TNode c = p.d_conj[ei];
      // exactly one unassigned variable? (vars precomputed, not re-collected)
      Node v;
      bool many = false;
      for (const Node& x : p.d_vars[ei])
      {
        if (a.find(x) == a.end())
        {
          if (!v.isNull())
          {
            many = true;
            break;
          }
          v = x;
        }
      }
      if (many || v.isNull())
      {
        continue;
      }
      // P(v) = lhs - rhs sampled at 0, 1, 2. If it is linear, P(v) = q + s*v.
      // v is written into `a` in place and erased again, so the assignment is
      // never copied.
      Integer pr[3];
      bool ok = true;
      for (int t = 0; t < 3 && ok; ++t)
      {
        a[v] = Integer(t);
        Cache ca;
        Integer l, r;
        ok = evalTerm(c[0], a, ca, l) && evalTerm(c[1], a, ca, r);
        if (ok)
        {
          pr[t] = l - r;
        }
      }
      a.erase(v);
      if (!ok)
      {
        continue;
      }
      Integer q = pr[0];
      Integer sl = pr[1] - pr[0];
      if (sl.sgn() == 0 || pr[2] != q + sl * Integer(2))
      {
        // constant in v, or genuinely nonlinear in v: not a definition
        continue;
      }
      if (!sl.divides(q))
      {
        // the definition exists over Q but not over Z: leave v to the search
        continue;
      }
      a[v] = -(q.exactQuotient(sl));
      prog = true;
    }
  }
}

void ArithWitnessSearch::complete(const Problem& p,
                                  const std::vector<Node>& vars,
                                  const std::vector<Node>& rootOrder,
                                  const Assign& roots,
                                  Assign& out) const
{
  out.clear();
  propagate(p, out);
  for (const Node& v : rootOrder)
  {
    if (out.find(v) != out.end())
    {
      // already determined by the roots fixed before it
      continue;
    }
    Assign::const_iterator it = roots.find(v);
    out[v] = (it == roots.end()) ? Integer(0) : it->second;
    propagate(p, out);
  }
  for (const Node& v : vars)
  {
    if (out.find(v) == out.end())
    {
      out[v] = Integer(0);
    }
  }
  propagate(p, out);
}

bool ArithWitnessSearch::costOf(const Problem& p,
                                const Assign& a,
                                size_t& nbad,
                                Integer& total) const
{
  nbad = 0;
  total = Integer(0);
  // one memo for the whole sweep: the assignment is fixed here
  Cache ca;
  for (const Node& c : p.d_conj)
  {
    Integer pen;
    if (!evalPenalty(c, a, ca, pen))
    {
      // Outside the fast fragment (an EXP axiom carrying an ite, say). It is
      // NOT scored -- but it is not waved through either: the final check runs
      // the rewriter over the ORIGINAL assertions, and that is what decides.
      continue;
    }
    if (pen.sgn() != 0)
    {
      ++nbad;
      total = total + pen;
    }
  }
  return true;
}

bool ArithWitnessSearch::enumerateWidths(
    const Problem& p,
    const std::vector<Node>& vars,
    uint64_t budget,
    const std::function<bool(const Assign&)>& verified,
    Assign& found)
{
  // Width variables: every v occurring as the exponent of a power of two
  // that is used as a MODULUS, `x mod 2^v`. A power of two elsewhere is a
  // shift amount (`x * 2^s`), and s ranges over [0, 2^k) like any operand.
  std::unordered_set<Node> wset;
  {
    std::unordered_set<TNode> visited;
    std::vector<TNode> visit(p.d_conj.begin(), p.d_conj.end());
    while (!visit.empty())
    {
      TNode cur = visit.back();
      visit.pop_back();
      if (!visited.insert(cur).second)
      {
        continue;
      }
      Kind ck = cur.getKind();
      if ((ck == Kind::INTS_MODULUS || ck == Kind::INTS_MODULUS_TOTAL)
          && cur[1].getKind() == Kind::EXP && cur[1][0].isConst()
          && cur[1][0].getConst<Rational>() == Rational(2)
          && cur[1][1].isVar())
      {
        wset.insert(cur[1][1]);
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  }
  std::vector<Node> wv, ov;
  for (const Node& v : vars)
  {
    (wset.find(v) != wset.end() ? wv : ov).push_back(v);
  }
  if (wv.empty())
  {
    return false;
  }
  // The rewriter check is far dearer than the fast evaluator, and a conjunct
  // outside the evaluator's fragment scores as satisfied, so cap how many
  // candidates may reach it.
  const uint64_t maxVerify = 64;
  uint64_t spent = 0, nverify = 0;
  uint64_t rnd = 0x2545f4914f6cdd1dULL;
  for (uint32_t w = 1; w <= 32 && spent < budget; ++w)
  {
    const Integer n = Integer(2).pow(w);
    const uint64_t left = budget - spent;
    Integer space = n.pow(ov.size());
    const bool exhaustive = space <= Integer(left);
    const uint64_t count =
        exhaustive ? space.getUnsigned64() : left;
    Assign cand;
    for (const Node& v : wv)
    {
      cand[v] = Integer(w);
    }
    std::vector<uint64_t> digit(ov.size(), 0);
    const uint64_t nn = n.getUnsigned64();  // w <= 32
    for (uint64_t i = 0; i < count; ++i, ++spent)
    {
      for (size_t j = 0; j < ov.size(); ++j)
      {
        uint64_t d = exhaustive ? digit[j] : (nextRand(rnd) % nn);
        cand[ov[j]] = Integer(d);
      }
      if (exhaustive)
      {
        // odometer
        for (size_t j = 0; j < ov.size(); ++j)
        {
          if (++digit[j] < nn)
          {
            break;
          }
          digit[j] = 0;
        }
      }
      size_t nbad;
      Integer tot;
      costOf(p, cand, nbad, tot);
      if (nbad != 0)
      {
        continue;
      }
      if (++nverify > maxVerify)
      {
        return false;
      }
      if (verified(cand))
      {
        found = cand;
        ++d_stats.d_numEnumSolved;
        return true;
      }
    }
  }
  return false;
}

PreprocessingPassResult ArithWitnessSearch::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  uint64_t budget = options().arith.arithWitnessSearch;
  const uint64_t enumBudget = options().arith.arithWitnessEnum;
  if (budget == 0 && enumBudget == 0)
  {
    return PreprocessingPassResult::NO_CONFLICT;
  }
  AssertionPipeline* ap = assertionsToPreprocess;
  NodeManager* nm = nodeManager();

  Problem prob;
  std::vector<Node>& cs = prob.d_conj;
  for (size_t i = 0, n = ap->size(); i < n; ++i)
  {
    if (expr::hasBoundVar((*ap)[i]))
    {
      // quantified input: witness synthesis says nothing about it
      return PreprocessingPassResult::NO_CONFLICT;
    }
    collectConjuncts((*ap)[i], cs);
  }
  if (cs.empty())
  {
    return PreprocessingPassResult::NO_CONFLICT;
  }

  std::unordered_set<Node> vset;
  {
    std::unordered_set<TNode> visited;
    for (const Node& c : cs)
    {
      collectVars(c, vset, visited);
    }
  }
  std::vector<Node> vars(vset.begin(), vset.end());
  std::sort(vars.begin(), vars.end());
  if (vars.empty())
  {
    return PreprocessingPassResult::NO_CONFLICT;
  }

  // Per-conjunct variables and the equality index, computed once. Recomputing
  // these inside propagate is what made the search quadratic.
  prob.d_vars.resize(cs.size());
  for (size_t i = 0, n = cs.size(); i < n; ++i)
  {
    std::unordered_set<Node> vs;
    std::unordered_set<TNode> visited;
    collectVars(cs[i], vs, visited);
    prob.d_vars[i].assign(vs.begin(), vs.end());
    std::sort(prob.d_vars[i].begin(), prob.d_vars[i].end());
    if (cs[i].getKind() == Kind::EQUAL && cs[i].getNumChildren() == 2
        && cs[i][0].getType().isInteger())
    {
      prob.d_eqs.push_back(i);
    }
  }

  const bool signedSearch = options().arith.arithWitnessSearchSigned;

  // Satisfies `c` when the single variable `v` is set to `k`?
  auto holdsAt = [&](TNode c, const Node& v, const Integer& k) {
    Assign probe;
    probe[v] = k;
    Cache ca;
    Integer pen;
    return evalPenalty(c, probe, ca, pen) && pen.sgn() == 0;
  };

  // Lower bound implied by the unit constraints on a single variable, which is
  // where the roots want to start (`it13 >= 1`, `it1 = 2`, ...).
  //
  // `lower` is the starting point; `floors` is what the hill-climb refuses to
  // move below. They are the same map by default. The probe below scans
  // UPWARD from 0, so the value it returns is the least satisfying value in
  // [0,8] -- which is a genuine lower bound for a constraint that bounds
  // below, and simply the wrong answer for one that bounds above (`it5 <= 0`
  // returns 0, pinning it5 to 0 for the whole search). Under
  // --arith-witness-search-signed a floor is installed only after being
  // checked, so a constraint satisfied somewhere below contributes a starting
  // point but no bound.
  std::unordered_map<Node, Integer> lower, floors;
  for (size_t i = 0, n = cs.size(); i < n; ++i)
  {
    if (prob.d_vars[i].size() != 1)
    {
      continue;
    }
    Node c = cs[i];
    Node v = prob.d_vars[i][0];
    for (int k = 0; k <= 8; ++k)
    {
      if (!holdsAt(c, v, Integer(k)))
      {
        continue;
      }
      std::unordered_map<Node, Integer>::iterator it = lower.find(v);
      if (it == lower.end() || Integer(k) > it->second)
      {
        lower[v] = Integer(k);
      }
      bool isFloor = true;
      if (signedSearch)
      {
        // Everything in [0,k) already failed. Check below 0, and far below,
        // since `c` may be satisfied only deep in the negatives.
        static const int64_t sentinels[4] = {-16, -256, -65536, -2147483648LL};
        for (int j = 1; isFloor && j <= 8; ++j)
        {
          isFloor = !holdsAt(c, v, Integer(k - j));
        }
        for (int j = 0; isFloor && j < 4; ++j)
        {
          isFloor = !holdsAt(c, v, Integer(sentinels[j]));
        }
      }
      if (isFloor)
      {
        std::unordered_map<Node, Integer>::iterator ft = floors.find(v);
        if (ft == floors.end() || Integer(k) > ft->second)
        {
          floors[v] = Integer(k);
        }
      }
      break;
    }
  }

  // How many equalities each variable appears in. A variable at the SOURCE of
  // the definition chain appears in very few, so this orders roots before the
  // quantities derived from them.
  std::unordered_map<Node, size_t> eqCount;
  for (size_t ei : prob.d_eqs)
  {
    for (const Node& v : prob.d_vars[ei])
    {
      eqCount[v] += 1;
    }
  }
  struct ByRank
  {
    const std::unordered_map<Node, size_t>* d_c;
    bool operator()(const Node& x, const Node& y) const
    {
      std::unordered_map<Node, size_t>::const_iterator a = d_c->find(x);
      std::unordered_map<Node, size_t>::const_iterator b = d_c->find(y);
      size_t ca = (a == d_c->end()) ? 0 : a->second;
      size_t cb = (b == d_c->end()) ? 0 : b->second;
      return ca != cb ? ca < cb : x < y;
    }
  };
  ByRank byRank{&eqCount};

  // Determine the ROOT SET by the same incremental procedure that `complete`
  // will replay: fix one variable, propagate, and only then look at what is
  // still undetermined. Bounded variables go first -- they are the ones the
  // problem actually constrains, and letting them be DERIVED instead tends to
  // drive them below their own lower bound.
  std::vector<Node> boundedVars, otherVars;
  for (const Node& v : vars)
  {
    (lower.count(v) ? boundedVars : otherVars).push_back(v);
  }
  std::sort(boundedVars.begin(), boundedVars.end(), byRank);
  std::sort(otherVars.begin(), otherVars.end(), byRank);

  std::vector<Node> rootOrder;
  Assign rootVals;
  {
    Assign a;
    propagate(prob, a);
    for (int phase = 0; phase < 2; ++phase)
    {
      const std::vector<Node>& pool = (phase == 0) ? boundedVars : otherVars;
      for (const Node& v : pool)
      {
        if (a.find(v) != a.end())
        {
          continue;
        }
        std::unordered_map<Node, Integer>::const_iterator it = lower.find(v);
        Integer val = (it == lower.end()) ? Integer(0) : it->second;
        a[v] = val;
        rootOrder.push_back(v);
        rootVals[v] = val;
        propagate(prob, a);
      }
    }
  }

  // No structural precondition is imposed on the root fraction. An earlier
  // version skipped problems where most variables were roots, on the theory
  // that only triangular systems are worth trying; it also skipped twn05 and
  // two size04 instances that the search solves. Cost is bounded by the
  // evaluation budget instead, which is the thing that actually costs time.

  Assign cur;
  complete(prob, vars, rootOrder, rootVals, cur);
  size_t bestBad = 0;
  Integer bestTot;
  if (!costOf(prob, cur, bestBad, bestTot))
  {
    ++d_stats.d_numFailed;
    return PreprocessingPassResult::NO_CONFLICT;
  }

  const int64_t deltas[5] = {1, -1, 2, -2, 4};
  uint64_t rnd = 0x9e3779b97f4a7c15ULL;
  std::vector<Node> vs, vals;

  // A candidate is accepted only if the REWRITER agrees, over the original
  // assertions. The fast evaluator drives the search; it never decides.
  auto verified = [&](const Assign& cand) {
    vs.clear();
    vals.clear();
    for (const Node& v : vars)
    {
      Assign::const_iterator it = cand.find(v);
      if (it == cand.end())
      {
        return false;
      }
      vs.push_back(v);
      vals.push_back(nm->mkConstInt(Rational(it->second)));
    }
    for (size_t i = 0, n = ap->size(); i < n; ++i)
    {
      Node inst =
          (*ap)[i].substitute(vs.begin(), vs.end(), vals.begin(), vals.end());
      Node val = rewrite(inst);
      if (!val.isConst() || !val.getConst<bool>())
      {
        return false;
      }
    }
    return true;
  };

  Assign found;
  bool haveModel = false;
  if (enumBudget > 0)
  {
    haveModel = enumerateWidths(prob, vars, enumBudget, verified, found);
  }
  if (!haveModel && bestBad == 0 && verified(cur))
  {
    haveModel = true;
    found = cur;
  }
  if (!haveModel && rootOrder.empty())
  {
    // Propagation determined every variable and the result is not a model.
    // There is nothing left to vary, so the search has no move to make -- and
    // without this the loop below would spin without ever spending budget.
    ++d_stats.d_numFailed;
    return PreprocessingPassResult::NO_CONFLICT;
  }
  uint64_t evals = 0;
  for (uint64_t step = 0; evals < budget && !haveModel; ++step)
  {
    ++d_stats.d_numSteps;
    bool improved = false;

    // MIRROR MOVE: negate every root that no constraint bounds below, all at
    // once. These closed forms are polynomials of uniform total degree in the
    // unbounded variables, so the mirror point scores the SAME on the big
    // arithmetic constraint while flipping which side of zero the variables
    // sit on -- which is exactly what the sign-shaped unit constraints
    // (`it10 <= 0`) want. Single-variable moves cannot get there: flipping one
    // of a coupled pair breaks the sign pairing in the cross terms and scores
    // far worse than either end, so the search sits in the wrong orthant at a
    // penalty of 1 forever. Like every other move it is accepted only on a
    // strict improvement, so where the symmetry does not hold it costs one
    // evaluation per sweep and nothing else.
    if (signedSearch)
    {
      Assign trial = rootVals;
      bool anyFlip = false;
      for (const Node& v : rootOrder)
      {
        if (floors.count(v) || trial[v].sgn() == 0)
        {
          continue;
        }
        trial[v] = -trial[v];
        anyFlip = true;
      }
      if (anyFlip)
      {
        Assign cand;
        complete(prob, vars, rootOrder, trial, cand);
        size_t nb;
        Integer tot;
        ++evals;
        if (costOf(prob, cand, nb, tot)
            && (nb < bestBad || (nb == bestBad && tot < bestTot)))
        {
          bestBad = nb;
          bestTot = tot;
          rootVals = trial;
          cur = cand;
          improved = true;
          if (nb == 0 && verified(cand))
          {
            haveModel = true;
            found = cand;
          }
        }
      }
    }

    // one randomised sweep over the roots; take the first strict improvement
    size_t nr = rootOrder.size();
    size_t start = nr ? size_t(nextRand(rnd) % nr) : 0;
    for (size_t idx = 0; idx < nr && !improved && !haveModel; ++idx)
    {
      const Node& v = rootOrder[(start + idx) % nr];
      // The 6th move is the SIGN FLIP v -> -v. The step moves are +-1, +-2, +4,
      // so a root that has settled at a positive value can only reach its
      // mirror by walking through the intervening points, and in these
      // problems those points are all worse than both ends.
      const int nmoves = signedSearch ? 6 : 5;
      for (int di = 0; di < nmoves; ++di)
      {
        Integer nv = (di == 5) ? -rootVals[v] : rootVals[v] + Integer(deltas[di]);
        if (nv == rootVals[v])
        {
          continue;
        }
        std::unordered_map<Node, Integer>::const_iterator lb = floors.find(v);
        if (lb != floors.end() && nv < lb->second)
        {
          continue;
        }
        Assign trial = rootVals;
        trial[v] = nv;
        Assign cand;
        complete(prob, vars, rootOrder, trial, cand);
        size_t nb;
        Integer tot;
        ++evals;
        if (!costOf(prob, cand, nb, tot))
        {
          continue;
        }
        if (evals >= budget)
        {
          idx = nr;  // out of budget mid-sweep
        }
        if (nb < bestBad || (nb == bestBad && tot < bestTot))
        {
          bestBad = nb;
          bestTot = tot;
          rootVals = trial;
          cur = cand;
          improved = true;
          if (nb == 0 && verified(cand))
          {
            haveModel = true;
            found = cand;
          }
          break;
        }
      }
    }
    if (!haveModel && (!improved || bestBad == 0) && !rootOrder.empty())
    {
      // Plateau, or a zero-penalty point the rewriter rejected: kick a root.
      const Node& v = rootOrder[nextRand(rnd) % rootOrder.size()];
      int64_t mag = int64_t(1 + nextRand(rnd) % 3);
      // The kick is upward-only by default. That is what keeps a root which
      // has settled at a positive value from ever being carried across zero.
      if (signedSearch && (nextRand(rnd) & 1) != 0)
      {
        mag = -mag;
      }
      Integer kick = rootVals[v] + Integer(mag);
      std::unordered_map<Node, Integer>::const_iterator kb = floors.find(v);
      if (kb != floors.end() && kick < kb->second)
      {
        kick = kb->second;
      }
      rootVals[v] = kick;
      Assign kicked;
      complete(prob, vars, rootOrder, rootVals, kicked);
      cur = kicked;
      ++evals;
      if (!costOf(prob, cur, bestBad, bestTot))
      {
        break;
      }
      if (bestBad == 0 && verified(cur))
      {
        haveModel = true;
        found = cur;
      }
    }
  }

  if (!haveModel)
  {
    ++d_stats.d_numFailed;
    return PreprocessingPassResult::NO_CONFLICT;
  }
  // rebuild vs/vals for the accepted model
  vs.clear();
  vals.clear();
  for (const Node& v : vars)
  {
    vs.push_back(v);
    vals.push_back(nm->mkConstInt(Rational(found[v])));
  }

  // Verified model: the problem is satisfiable, and this is a witness.
  for (size_t i = 0, n = vs.size(); i < n; ++i)
  {
    d_preprocContext->addSubstitution(vs[i], vals[i]);
  }
  for (size_t i = 0, n = ap->size(); i < n; ++i)
  {
    ap->replace(i, nm->mkConst(true));
  }
  ++d_stats.d_numSolved;
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
