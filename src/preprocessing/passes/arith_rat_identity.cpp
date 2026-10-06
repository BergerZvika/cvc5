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
      if (k == Kind::DIVISION || k == Kind::DIVISION_TOTAL)
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
