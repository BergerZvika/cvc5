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
 * Implementation of the arith-rat-identity preprocessing pass.
 */

#include "preprocessing/passes/arith_rat_identity.h"

#include <functional>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node_algorithm.h"
#include "options/arith_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

namespace {

/** A fraction num / den of arithmetic terms. */
struct Frac
{
  Node num;
  Node den;
};

/**
 * Split an exponent into a non-constant part and a constant offset. Returns
 * false for a constant exponent, which has no group to join.
 */
bool splitOffset(NodeManager* nm, TNode e, Node& rest, Integer& c)
{
  if (e.isConst())
  {
    return false;
  }
  c = Integer(0);
  if (e.getKind() != Kind::ADD)
  {
    rest = e;
    return true;
  }
  std::vector<Node> others;
  for (const Node& x : e)
  {
    if (x.isConst() && x.getConst<Rational>().isIntegral())
    {
      c += x.getConst<Rational>().getNumerator();
    }
    else
    {
      others.push_back(x);
    }
  }
  rest = others.size() == 1 ? others[0] : nm->mkNode(Kind::ADD, others);
  return true;
}

/**
 * Split a normalized exponent into integer multiples of its monomials plus a
 * constant. Returns false when a coefficient is not an integer.
 */
bool splitMonomials(TNode e, std::map<Node, Integer>& coefs, Integer& c)
{
  c = Integer(0);
  std::vector<TNode> terms;
  if (e.getKind() == Kind::ADD)
  {
    terms.insert(terms.end(), e.begin(), e.end());
  }
  else
  {
    terms.push_back(e);
  }
  NodeManager* nm = e.getNodeManager();
  for (TNode t : terms)
  {
    if (t.isConst())
    {
      const Rational& r = t.getConst<Rational>();
      if (!r.isIntegral())
      {
        return false;
      }
      c += r.getNumerator();
      continue;
    }
    Integer a(1);
    Node m = t;
    if (t.getKind() == Kind::MULT && t[0].isConst())
    {
      const Rational& r = t[0].getConst<Rational>();
      if (!r.isIntegral())
      {
        return false;
      }
      a = r.getNumerator();
      std::vector<Node> rest(t.begin() + 1, t.end());
      m = rest.size() == 1 ? rest[0] : nm->mkNode(Kind::MULT, rest);
    }
    coefs[m] += a;
  }
  return true;
}

/** A polynomial over integer atoms: monomial (atom -> degree) -> coefficient. */
using Mono = std::map<Node, uint32_t>;
using Poly = std::map<Mono, Rational>;

/** Bound on the monomials of a polynomial built by exactDiv. */
const size_t s_polyCap = 4096;

void polyAdd(Poly& p, const Poly& q, const Rational& c = Rational(1))
{
  for (const auto& [m, a] : q)
  {
    Rational& r = p[m];
    r += c * a;
    if (r.isZero())
    {
      p.erase(m);
    }
  }
}

Poly polyMul(const Poly& p, const Poly& q)
{
  Poly r;
  for (const auto& [m1, a1] : p)
  {
    for (const auto& [m2, a2] : q)
    {
      Mono m = m1;
      for (const auto& [v, k] : m2)
      {
        m[v] += k;
      }
      Rational& c = r[m];
      c += a1 * a2;
      if (c.isZero())
      {
        r.erase(m);
      }
    }
  }
  return r;
}

Poly polyConst(const Rational& c)
{
  Poly p;
  if (!c.isZero())
  {
    p[Mono()] = c;
  }
  return p;
}

Poly polyAtom(const Node& a)
{
  Poly p;
  p[Mono{{a, 1}}] = Rational(1);
  return p;
}

/**
 * The polynomial of the integer term t, reading t through subs. Fails on a
 * non-integer atom or when the polynomial grows past s_polyCap.
 */
bool polyOf(TNode t,
            const std::unordered_map<TNode, Node>& subs,
            std::unordered_map<TNode, Poly>& cache,
            Poly& out)
{
  auto it = cache.find(t);
  if (it != cache.end())
  {
    out = it->second;
    return true;
  }
  auto sit = subs.find(t);
  Kind k = t.getKind();
  Poly r;
  if (sit != subs.end())
  {
    if (!polyOf(sit->second, subs, cache, r))
    {
      return false;
    }
  }
  else if (t.isConst())
  {
    const Rational& c = t.getConst<Rational>();
    if (!c.isIntegral())
    {
      return false;
    }
    r = polyConst(c);
  }
  else if (k == Kind::ADD || k == Kind::SUB)
  {
    for (size_t i = 0, n = t.getNumChildren(); i < n; ++i)
    {
      Poly q;
      if (!polyOf(t[i], subs, cache, q))
      {
        return false;
      }
      polyAdd(r, q, Rational(k == Kind::SUB && i > 0 ? -1 : 1));
    }
  }
  else if (k == Kind::NEG)
  {
    Poly q;
    if (!polyOf(t[0], subs, cache, q))
    {
      return false;
    }
    polyAdd(r, q, Rational(-1));
  }
  else if (k == Kind::MULT || k == Kind::NONLINEAR_MULT)
  {
    r = polyConst(Rational(1));
    for (const Node& c : t)
    {
      Poly q;
      if (!polyOf(c, subs, cache, q))
      {
        return false;
      }
      r = polyMul(r, q);
      if (r.size() > s_polyCap)
      {
        return false;
      }
    }
  }
  else if (t.getType().isInteger())
  {
    r = polyAtom(t);
  }
  else
  {
    return false;
  }
  cache[t] = r;
  out = r;
  return true;
}

/** p with every occurrence of the atom a replaced by q. */
bool polySubst(const Poly& p, const Node& a, const Poly& q, Poly& out)
{
  out.clear();
  std::vector<Poly> pows{polyConst(Rational(1))};
  for (const auto& [m, c] : p)
  {
    Mono rest = m;
    uint32_t d = 0;
    auto it = rest.find(a);
    if (it != rest.end())
    {
      d = it->second;
      rest.erase(it);
    }
    while (pows.size() <= d)
    {
      pows.push_back(polyMul(pows.back(), q));
      if (pows.back().size() > s_polyCap)
      {
        return false;
      }
    }
    Poly term;
    term[rest] = c;
    polyAdd(out, polyMul(term, pows[d]));
    if (out.size() > s_polyCap)
    {
      return false;
    }
  }
  return true;
}

/**
 * Whether p takes integer values at every integer point: its coefficients in
 * the basis of products of binomials C(x, i) are integers. x^k is
 * sum_i S(k,i) i! C(x,i), S the Stirling numbers of the second kind.
 */
bool polyIntValued(const Poly& p)
{
  // st[k][i] = S(k,i) * i!
  std::vector<std::vector<Integer>> st{{Integer(1)}};
  std::map<std::vector<std::pair<Node, uint32_t>>, Rational> basis;
  for (const auto& [m, c] : p)
  {
    std::vector<std::pair<std::vector<std::pair<Node, uint32_t>>, Rational>>
        acc{{{}, c}};
    for (const auto& [v, k] : m)
    {
      if (k > 32)
      {
        return false;
      }
      while (st.size() <= k)
      {
        // S(k+1,i) i! = i * (S(k,i) + S(k,i-1)) (i-1)! ... in closed form:
        // T(k+1,i) = i * (T(k,i) + T(k,i-1)) with T(k,i) = S(k,i) i!
        const std::vector<Integer>& prev = st.back();
        std::vector<Integer> next(prev.size() + 1, Integer(0));
        for (size_t i = 1; i < next.size(); ++i)
        {
          Integer a = i < prev.size() ? prev[i] : Integer(0);
          next[i] = Integer(i) * (a + prev[i - 1]);
        }
        st.push_back(next);
      }
      std::vector<std::pair<std::vector<std::pair<Node, uint32_t>>, Rational>>
          nacc;
      for (const auto& [key, a] : acc)
      {
        for (uint32_t i = 0; i <= k; ++i)
        {
          if (st[k][i].isZero())
          {
            continue;
          }
          auto nkey = key;
          nkey.push_back({v, i});
          nacc.push_back({nkey, a * Rational(st[k][i])});
        }
      }
      acc.swap(nacc);
    }
    for (const auto& [key, a] : acc)
    {
      std::vector<std::pair<Node, uint32_t>> nkey;
      for (const auto& e : key)
      {
        if (e.second > 0)
        {
          nkey.push_back(e);
        }
      }
      basis[nkey] += a;
    }
  }
  for (const auto& [key, a] : basis)
  {
    if (!a.isIntegral())
    {
      return false;
    }
  }
  return true;
}

/**
 * Whether the integer division div(N, D) is exact, i.e. D divides N. For a
 * constant D, N / D must be integer-valued. Otherwise D must be +-(s-1)^j for
 * the base s of a power E = exp(s, m) that is the only power of base s in N;
 * for m >= 0 the binomial theorem gives E = T + (s-1)^j * q with
 * T = sum_{i<j} C(m,i) (s-1)^i and q an integer, so D divides N when it
 * divides N[E := T] -- as a polynomial in s, with an integer-valued quotient.
 * The guard m >= 0 is appended to guards.
 */
bool exactDiv(NodeManager* nm,
              TNode t,
              const std::unordered_map<TNode, Node>& subs,
              std::unordered_map<TNode, Poly>& cache,
              std::vector<Node>& guards)
{
  Poly pN, pD;
  if (!polyOf(t[0], subs, cache, pN) || !polyOf(t[1], subs, cache, pD)
      || pD.empty())
  {
    return false;
  }
  if (pD.size() == 1 && pD.begin()->first.empty())
  {
    Poly q;
    polyAdd(q, pN, Rational(1) / pD.begin()->second);
    if (polyIntValued(q))
    {
      return true;
    }
  }
  std::unordered_set<Node> exps;
  for (const auto& [m, c] : pN)
  {
    for (const auto& [v, k] : m)
    {
      if (v.getKind() == Kind::EXP)
      {
        exps.insert(v);
      }
    }
  }
  for (const Node& e : exps)
  {
    Node s = e[0];
    bool unique = true;
    for (const Node& o : exps)
    {
      unique = unique && (o == e || o[0] != s);
    }
    Poly pS, pM;
    if (!unique || !polyOf(s, subs, cache, pS) || !polyOf(e[1], subs, cache, pM))
    {
      continue;
    }
    // the base is an atom or a constant
    bool sConst = pS.empty() || (pS.size() == 1 && pS.begin()->first.empty());
    bool sAtom = pS.size() == 1 && pS.begin()->second == Rational(1)
                 && pS.begin()->first.size() == 1
                 && pS.begin()->first.begin()->second == 1;
    if (!sConst && !sAtom)
    {
      continue;
    }
    Poly pB = pS;
    polyAdd(pB, polyConst(Rational(-1)));
    if (pB.empty())
    {
      continue;
    }
    // j with pD = +-pB^j
    uint32_t j = 0;
    int sign = 0;
    Poly pw = polyConst(Rational(1));
    for (uint32_t i = 1; i <= 16 && sign == 0; ++i)
    {
      pw = polyMul(pw, pB);
      Poly neg;
      polyAdd(neg, pw, Rational(-1));
      if (pw == pD || neg == pD)
      {
        j = i;
        sign = pw == pD ? 1 : -1;
      }
    }
    if (sign == 0)
    {
      continue;
    }
    // T = sum_{i<j} C(m,i) pB^i
    Poly pT, binom = polyConst(Rational(1)), pBi = polyConst(Rational(1));
    for (uint32_t i = 0; i < j; ++i)
    {
      polyAdd(pT, polyMul(binom, pBi));
      Poly f = pM;
      polyAdd(f, polyConst(Rational(-static_cast<int>(i))));
      binom = polyMul(binom, f);
      Poly sc;
      polyAdd(sc, binom, Rational(1, static_cast<int>(i + 1)));
      binom = sc;
      pBi = polyMul(pBi, pB);
    }
    Poly pNT;
    if (!polySubst(pN, e, pT, pNT))
    {
      continue;
    }
    Poly quot;
    if (sConst)
    {
      polyAdd(quot, pNT, Rational(1) / pD.begin()->second);
    }
    else
    {
      // read s as b + 1 and divide by b^j
      Node sv = pS.begin()->first.begin()->first;
      Node b = nm->mkBoundVar("b", nm->integerType());
      Poly bp1 = polyAtom(b);
      polyAdd(bp1, polyConst(Rational(1)));
      Poly pNb;
      if (!polySubst(pNT, sv, bp1, pNb))
      {
        continue;
      }
      bool ok = true;
      for (const auto& [m, c] : pNb)
      {
        auto it = m.find(b);
        if (it == m.end() || it->second < j)
        {
          ok = false;
          break;
        }
        Mono mq = m;
        if (it->second == j)
        {
          mq.erase(b);
        }
        else
        {
          mq[b] = it->second - j;
        }
        quot[mq] = c * Rational(sign);
      }
      if (!ok)
      {
        continue;
      }
    }
    if (polyIntValued(quot))
    {
      guards.push_back(
          nm->mkNode(Kind::GEQ, e[1], nm->mkConstInt(Rational(0))));
      return true;
    }
  }
  return false;
}

/**
 * Exact division of p by d over Q, as polynomials: the quotient q with
 * p = d * q, by long division in an atom z of d whose leading coefficient is
 * a constant. Fails on a non-zero remainder.
 */
bool polyDivExact(const Poly& p, const Poly& d, Poly& q)
{
  q.clear();
  if (d.empty())
  {
    return false;
  }
  if (d.size() == 1 && d.begin()->first.empty())
  {
    polyAdd(q, p, Rational(1) / d.begin()->second);
    return true;
  }
  // the main variable z and the degree of d in it
  Node z;
  uint32_t dz = 0;
  for (const auto& [m, c] : d)
  {
    for (const auto& [v, k] : m)
    {
      if (k > dz)
      {
        z = v;
        dz = k;
      }
    }
  }
  // the leading coefficient of d in z must be a constant
  Rational lc;
  for (const auto& [m, c] : d)
  {
    auto it = m.find(z);
    if (it != m.end() && it->second == dz)
    {
      if (m.size() != 1 || !lc.isZero())
      {
        return false;
      }
      lc = c;
    }
  }
  Poly r = p;
  for (size_t iter = 0; !r.empty(); ++iter)
  {
    if (iter > s_polyCap || r.size() > s_polyCap)
    {
      return false;
    }
    // a term of r of highest degree in z
    const Mono* lm = nullptr;
    uint32_t lz = 0;
    for (const auto& [m, c] : r)
    {
      auto it = m.find(z);
      uint32_t k = it == m.end() ? 0 : it->second;
      if (lm == nullptr || k > lz)
      {
        lm = &m;
        lz = k;
      }
    }
    if (lz < dz)
    {
      return false;
    }
    Mono tm = *lm;
    if (lz == dz)
    {
      tm.erase(z);
    }
    else
    {
      tm[z] = lz - dz;
    }
    Poly t;
    t[tm] = r.at(*lm) / lc;
    polyAdd(q, t);
    polyAdd(r, polyMul(t, d), Rational(-1));
  }
  return true;
}

/**
 * Whether div(N, D) is exact, by induction on the exponent. N must be
 * C * E + R(v) for the only power E = exp(s, v + c) of base s in N, where v is
 * an atom, and C, s and D do not mention v. Then for v + c >= 0:
 *   base  (v = -c, E = 1):  D divides C + R(-c)
 *   step  (E(v+1) = s E(v)): N(v+1) - s N(v) = R(v+1) - s R(v), divisible by D
 * each with an integer-valued quotient, so D divides N for every v >= -c.
 * The guard v + c >= 0 is appended to guards.
 */
bool exactDivInduction(NodeManager* nm,
                       TNode t,
                       const std::unordered_map<TNode, Node>& subs,
                       std::unordered_map<TNode, Poly>& cache,
                       std::vector<Node>& guards)
{
  Poly pN, pD;
  if (!polyOf(t[0], subs, cache, pN) || !polyOf(t[1], subs, cache, pD)
      || pD.empty())
  {
    return false;
  }
  std::unordered_set<Node> exps;
  for (const auto& [m, c] : pN)
  {
    for (const auto& [v, k] : m)
    {
      if (v.getKind() == Kind::EXP)
      {
        exps.insert(v);
      }
    }
  }
  for (const Node& e : exps)
  {
    Poly pM;
    if (!polyOf(e[1], subs, cache, pM))
    {
      continue;
    }
    // the exponent is v + c
    Node v;
    Rational c;
    bool ok = true;
    for (const auto& [m, a] : pM)
    {
      if (m.empty())
      {
        c = a;
      }
      else if (v.isNull() && m.size() == 1 && m.begin()->second == 1
               && a == Rational(1))
      {
        v = m.begin()->first;
      }
      else
      {
        ok = false;
      }
    }
    if (!ok || v.isNull() || expr::hasSubterm(e[0], v))
    {
      continue;
    }
    // no other atom of N or D mentions v or E; C does not mention v
    Poly pC, pR;
    for (const auto& [m, a] : pN)
    {
      auto it = m.find(e);
      uint32_t de = it == m.end() ? 0 : it->second;
      for (const auto& [x, k] : m)
      {
        ok = ok && (x == v || x == e || !expr::hasSubterm(x, v));
      }
      if (de > 1 || (de == 1 && m.count(v)))
      {
        ok = false;
      }
      Mono rest = m;
      rest.erase(e);
      (de == 1 ? pC : pR)[rest] = a;
    }
    for (const auto& [m, a] : pD)
    {
      for (const auto& [x, k] : m)
      {
        ok = ok && x != e && !expr::hasSubterm(x, v);
      }
    }
    if (!ok)
    {
      continue;
    }
    Poly pS;
    if (!polyOf(e[0], subs, cache, pS))
    {
      continue;
    }
    // base: v = -c, E = 1
    Poly base = pC, rBase, vNext = polyAtom(v), q;
    if (!polySubst(pR, v, polyConst(-c), rBase))
    {
      continue;
    }
    polyAdd(base, rBase);
    if (!polyDivExact(base, pD, q) || !polyIntValued(q))
    {
      continue;
    }
    // step: R(v+1) - s R(v)
    polyAdd(vNext, polyConst(Rational(1)));
    Poly step;
    if (!polySubst(pR, v, vNext, step))
    {
      continue;
    }
    polyAdd(step, polyMul(pS, pR), Rational(-1));
    if (!polyDivExact(step, pD, q) || !polyIntValued(q))
    {
      continue;
    }
    guards.push_back(nm->mkNode(Kind::GEQ, e[1], nm->mkConstInt(Rational(0))));
    return true;
  }
  return false;
}

/** The integer value of `n` if it is a constant integer >= 2. */
bool constBase(TNode n, Integer& b)
{
  if (!n.isConst() || !n.getType().isInteger())
  {
    return false;
  }
  b = n.getConst<Rational>().getNumerator();
  return b >= Integer(2);
}

}  // namespace

ArithRatIdentity::ArithRatIdentity(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "arith-rat-identity")
{
}

PreprocessingPassResult ArithRatIdentity::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager* nm = nodeManager();
  const bool exactDivOn = options().arith.arithExactDiv;
  const bool exactDivIndOn = options().arith.arithExactDivInduction;

  // The equalities to process, in order of first appearance.
  std::vector<Node> atoms;
  std::unordered_set<TNode> visited;
  for (const Node& a : assertionsToPreprocess->ref())
  {
    std::vector<TNode> visit{a};
    while (!visit.empty())
    {
      TNode cur = visit.back();
      visit.pop_back();
      if (!visited.insert(cur).second || cur.isClosure())
      {
        continue;
      }
      if (cur.getKind() == Kind::EQUAL && cur[0].getType().isRealOrInt()
          && !expr::hasBoundVar(cur))
      {
        atoms.push_back(cur);
        continue;
      }
      if (cur.getType().isBoolean())
      {
        for (const Node& c : cur)
        {
          visit.push_back(c);
        }
      }
    }
  }

  std::vector<Node> lemmas;
  for (const Node& atom : atoms)
  {
    std::vector<Node> guards;

    // Powers of one base whose exponents differ by a constant share the power
    // with the smallest offset.
    std::vector<TNode> exps;
    std::unordered_set<TNode> seen;
    std::vector<TNode> visit{atom};
    bool hasDiv = false;
    while (!visit.empty())
    {
      TNode cur = visit.back();
      visit.pop_back();
      if (!seen.insert(cur).second)
      {
        continue;
      }
      Kind k = cur.getKind();
      if (k == Kind::DIVISION || k == Kind::DIVISION_TOTAL
          || ((exactDivOn || exactDivIndOn)
              && (k == Kind::INTS_DIVISION
                  || k == Kind::INTS_DIVISION_TOTAL)))
      {
        hasDiv = true;
      }
      if (k == Kind::EXP)
      {
        exps.push_back(cur);
      }
      for (const Node& c : cur)
      {
        visit.push_back(c);
      }
    }
    std::unordered_map<TNode, Node> subs;

    // A constant base that is a power of a smaller one in the atom is read
    // over that root, b^e = r^(j*e) for e >= 0.
    std::vector<Integer> cbases;
    for (TNode e : exps)
    {
      Integer b;
      if (constBase(e[0], b))
      {
        cbases.push_back(b);
      }
    }
    // base node -> (term, exponent over that base, multiplicity j)
    std::map<Node, std::vector<std::pair<TNode, Node>>> byBase;
    std::map<Node, std::unordered_set<Node>> rests;
    std::unordered_set<Node> collapsedBase;
    for (TNode e : exps)
    {
      Node base = e[0];
      Node ex = e[1];
      Integer b;
      if (constBase(base, b))
      {
        for (const Integer& r : cbases)
        {
          if (r >= b)
          {
            continue;
          }
          Integer acc = r;
          uint32_t j = 1;
          while (acc < b && j < 64)
          {
            acc *= r;
            ++j;
          }
          if (acc == b)
          {
            base = nm->mkConstInt(Rational(r));
            ex = rewrite(
                nm->mkNode(Kind::MULT, nm->mkConstInt(Rational(j)), ex));
            collapsedBase.insert(base);
            break;
          }
        }
      }
      if (ex.isConst())
      {
        continue;
      }
      Node rest;
      Integer c;
      splitOffset(nm, ex, rest, c);
      byBase[base].push_back({e, ex});
      rests[base].insert(rest);
    }
    // Bases whose exponents differ by more than a constant, or that absorbed
    // a collapsed base, are expressed over the powers of their exponents'
    // monomials: s^(sum a_m m + c) = prod (s^m)^a_m * s^c, a negative
    // coefficient going to the denominator. Valid when every monomial and
    // every exponent is non-negative (so each power is ordinary
    // exponentiation) and, for a denominator, s != 0 -- the latter is the
    // divisor guard added below.
    std::unordered_set<TNode> handled;
    for (const auto& [base, mem] : byBase)
    {
      if (rests[base].size() < 2 && collapsedBase.count(base) == 0)
      {
        continue;
      }
      std::vector<std::pair<std::map<Node, Integer>, Integer>> dec;
      bool ok = true;
      for (const auto& m : mem)
      {
        std::map<Node, Integer> coefs;
        Integer c;
        ok = ok && splitMonomials(m.second, coefs, c);
        for (const auto& [mono, a] : coefs)
        {
          ok = ok && a.abs() <= Integer(d_shiftCap);
        }
        ok = ok && c.abs() <= Integer(d_shiftCap);
        dec.push_back({coefs, c});
      }
      if (!ok)
      {
        continue;
      }
      std::unordered_set<Node> monos;
      for (size_t i = 0, n = mem.size(); i < n; ++i)
      {
        TNode term = mem[i].first;
        guards.push_back(nm->mkNode(
            Kind::GEQ, term[1], nm->mkConstInt(Rational(0))));
        std::vector<Node> num, den;
        auto put = [&](std::vector<Node>& v, const Node& f, const Integer& k) {
          for (Integer q(0); q < k.abs(); q += 1)
          {
            v.push_back(f);
          }
        };
        for (const auto& [mono, a] : dec[i].first)
        {
          if (a.isZero())
          {
            continue;
          }
          if (monos.insert(mono).second)
          {
            guards.push_back(nm->mkNode(
                Kind::GEQ, mono, nm->mkConstInt(Rational(0))));
          }
          Node pw = rewrite(nm->mkNode(Kind::EXP, base, mono));
          put(a.sgn() > 0 ? num : den, pw, a);
        }
        put(dec[i].second.sgn() > 0 ? num : den, base, dec[i].second);
        auto prod = [&](const std::vector<Node>& v) {
          return v.empty() ? nm->mkConstInt(Rational(1))
                           : (v.size() == 1 ? v[0] : nm->mkNode(Kind::MULT, v));
        };
        Node r = den.empty() ? prod(num)
                             : nm->mkNode(Kind::DIVISION, prod(num), prod(den));
        if (r != term)
        {
          subs[term] = r;
        }
        handled.insert(term);
      }
    }

    std::map<std::pair<Node, Node>, std::vector<std::pair<TNode, Integer>>>
        groups;
    for (TNode e : exps)
    {
      if (handled.count(e))
      {
        continue;
      }
      Node rest;
      Integer c;
      if (splitOffset(nm, e[1], rest, c))
      {
        groups[{e[0], rest}].push_back({e, c});
      }
    }
    for (const auto& [key, mem] : groups)
    {
      Integer cmin = mem[0].second;
      Integer cmax = mem[0].second;
      for (const auto& m : mem)
      {
        cmin = m.second < cmin ? m.second : cmin;
        cmax = m.second > cmax ? m.second : cmax;
      }
      if (cmin == cmax || cmax - cmin > Integer(d_shiftCap))
      {
        continue;
      }
      Node eMin = nm->mkNode(
          Kind::ADD, key.second, nm->mkConstInt(Rational(cmin)));
      Node pMin = rewrite(nm->mkNode(Kind::EXP, key.first, eMin));
      guards.push_back(
          nm->mkNode(Kind::GEQ, eMin, nm->mkConstInt(Rational(0))));
      for (const auto& m : mem)
      {
        uint32_t d = (m.second - cmin).toUnsignedInt();
        std::vector<Node> fs(d, key.first);
        fs.push_back(pMin);
        Node r = fs.size() == 1 ? pMin : nm->mkNode(Kind::MULT, fs);
        if (r != m.first)
        {
          subs[m.first] = r;
        }
      }
    }
    if (!hasDiv && subs.empty() && handled.empty())
    {
      continue;
    }

    // L - R as a fraction, treating every non-arithmetic subterm as an atom.
    // A divisor y adds the guard y != 0.
    std::unordered_map<TNode, Frac> cache;
    std::unordered_map<TNode, Poly> polys;
    Node one = nm->mkConstInt(Rational(1));
    std::function<Frac(TNode)> frac = [&](TNode t) -> Frac {
      auto it = cache.find(t);
      if (it != cache.end())
      {
        return it->second;
      }
      Frac r;
      Kind k = t.getKind();
      auto sit = subs.find(t);
      if (sit != subs.end())
      {
        r = frac(sit->second);
      }
      else if (k == Kind::ADD || k == Kind::SUB)
      {
        Frac f = frac(t[0]);
        for (size_t i = 1, n = t.getNumChildren(); i < n; ++i)
        {
          Frac g = frac(t[i]);
          Node a = nm->mkNode(Kind::MULT, f.num, g.den);
          Node b = nm->mkNode(Kind::MULT, g.num, f.den);
          f = {nm->mkNode(k, a, b), nm->mkNode(Kind::MULT, f.den, g.den)};
        }
        r = f;
      }
      else if (k == Kind::NEG)
      {
        Frac f = frac(t[0]);
        r = {nm->mkNode(Kind::NEG, f.num), f.den};
      }
      else if (k == Kind::MULT || k == Kind::NONLINEAR_MULT)
      {
        std::vector<Node> ns, ds;
        for (const Node& c : t)
        {
          Frac f = frac(c);
          ns.push_back(f.num);
          ds.push_back(f.den);
        }
        r = {nm->mkNode(Kind::MULT, ns), nm->mkNode(Kind::MULT, ds)};
      }
      else if (k == Kind::TO_REAL)
      {
        r = frac(t[0]);
      }
      else if ((k == Kind::DIVISION || k == Kind::DIVISION_TOTAL)
               && !(t[1].isConst() && t[1].getConst<Rational>().isZero()))
      {
        Frac x = frac(t[0]);
        Frac y = frac(t[1]);
        guards.push_back(
            t[1].eqNode(nm->mkConstRealOrInt(t[1].getType(), Rational(0)))
                .notNode());
        r = {nm->mkNode(Kind::MULT, x.num, y.den),
             nm->mkNode(Kind::MULT, x.den, y.num)};
      }
      else if ((exactDivOn || exactDivIndOn)
               && (k == Kind::INTS_DIVISION || k == Kind::INTS_DIVISION_TOTAL)
               && ((exactDivOn && exactDiv(nm, t, subs, polys, guards))
                   || (exactDivIndOn
                       && exactDivInduction(nm, t, subs, polys, guards))))
      {
        // an exact div is the real division
        Frac x = frac(t[0]);
        Frac y = frac(t[1]);
        guards.push_back(
            t[1].eqNode(nm->mkConstInt(Rational(0))).notNode());
        r = {nm->mkNode(Kind::MULT, x.num, y.den),
             nm->mkNode(Kind::MULT, x.den, y.num)};
      }
      else
      {
        r = {t, one};
      }
      cache[t] = r;
      return r;
    };
    Frac lhs = frac(atom[0]);
    Frac rhs = frac(atom[1]);
    Node num = rewrite(nm->mkNode(Kind::SUB,
                                  nm->mkNode(Kind::MULT, lhs.num, rhs.den),
                                  nm->mkNode(Kind::MULT, rhs.num, lhs.den)));
    Node zero = nm->mkConstRealOrInt(num.getType(), Rational(0));
    Node body = atom.eqNode(num.eqNode(zero));
    Node g = guards.empty()
                 ? nm->mkConst(true)
                 : (guards.size() == 1 ? guards[0]
                                       : nm->mkNode(Kind::AND, guards));
    lemmas.push_back(nm->mkNode(Kind::IMPLIES, g, body));
  }

  for (const Node& l : lemmas)
  {
    Node r = rewrite(l);
    if (r.isConst() && r.getConst<bool>())
    {
      continue;
    }
    assertionsToPreprocess->push_back(r);
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
