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
 * See int_order_facts.h.
 *
 * Each unconditional top-level integer atom is normalized to `L >= 0` for a
 * linear polynomial L, then stored as either a bound on a single atom
 * (d_lb / d_ub) or a difference bound `x - y >= c` (d_diff).  The difference
 * bounds are closed transitively so that a chain `a < b < c` answers
 * `a <= c`.  Queries consult the difference store first and fall back to
 * interval arithmetic over the single-atom bounds.
 */

#include "preprocessing/passes/int_order_facts.h"

#include <iterator>

#include "util/integer.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

IntOrderFacts::IntOrderFacts(Env& env) : EnvObj(env) {}

IntOrderFacts::Lin IntOrderFacts::toLin(TNode n) const
{
  Lin r;
  Kind k = n.getKind();
  if (n.isConst() && n.getType().isInteger())
  {
    r.d_const = n.getConst<Rational>();
    return r;
  }
  if (k == Kind::ADD || k == Kind::SUB)
  {
    for (size_t i = 0, sz = n.getNumChildren(); i < sz; ++i)
    {
      Lin c = toLin(n[i]);
      bool neg = (k == Kind::SUB && i > 0);
      r.d_const += neg ? -c.d_const : c.d_const;
      for (const auto& [a, v] : c.d_coeffs)
      {
        r.d_coeffs[a] += neg ? -v : v;
      }
    }
  }
  else if (k == Kind::NEG)
  {
    Lin c = toLin(n[0]);
    r.d_const = -c.d_const;
    for (const auto& [a, v] : c.d_coeffs)
    {
      r.d_coeffs[a] = -v;
    }
  }
  else if (k == Kind::MULT || k == Kind::NONLINEAR_MULT)
  {
    // Only constant * linear is handled; anything else stays an opaque atom.
    Rational coeff(1);
    Node rest;
    bool ok = true;
    for (const Node& c : n)
    {
      if (c.isConst() && c.getType().isInteger())
      {
        coeff *= c.getConst<Rational>();
      }
      else if (rest.isNull())
      {
        rest = c;
      }
      else
      {
        ok = false;
        break;
      }
    }
    if (!ok)
    {
      r.d_coeffs[n] = Rational(1);
      return r;
    }
    if (rest.isNull())
    {
      r.d_const = coeff;
      return r;
    }
    Lin c = toLin(rest);
    r.d_const = coeff * c.d_const;
    for (const auto& [a, v] : c.d_coeffs)
    {
      r.d_coeffs[a] = coeff * v;
    }
  }
  else
  {
    r.d_coeffs[n] = Rational(1);
  }
  for (auto it = r.d_coeffs.begin(); it != r.d_coeffs.end();)
  {
    it = (it->second.sgn() == 0) ? r.d_coeffs.erase(it) : std::next(it);
  }
  return r;
}

IntOrderFacts::Lin IntOrderFacts::linSub(const Lin& a, const Lin& b)
{
  Lin r = a;
  r.d_const -= b.d_const;
  for (const auto& [n, v] : b.d_coeffs)
  {
    r.d_coeffs[n] -= v;
  }
  for (auto it = r.d_coeffs.begin(); it != r.d_coeffs.end();)
  {
    it = (it->second.sgn() == 0) ? r.d_coeffs.erase(it) : std::next(it);
  }
  return r;
}

void IntOrderFacts::addGeq(const Lin& d)
{
  // Keep any fact the difference-bound closure cannot hold, so provNonNeg can
  // still match it exactly. Two-variable forms are handled below as usual.
  if (d.d_coeffs.size() > 2)
  {
    d_general.push_back(d);
  }
  if (d.d_coeffs.size() == 1)
  {
    const Node& x = d.d_coeffs.begin()->first;
    const Rational& c = d.d_coeffs.begin()->second;
    if (c.sgn() > 0)
    {
      Rational v((-d.d_const / c).ceiling());
      auto it = d_lb.find(x);
      if (it == d_lb.end() || v > it->second) d_lb[x] = v;
    }
    else
    {
      Rational v((d.d_const / (-c)).floor());
      auto it = d_ub.find(x);
      if (it == d_ub.end() || v < it->second) d_ub[x] = v;
    }
    return;
  }
  if (d.d_coeffs.size() == 2)
  {
    auto i0 = d.d_coeffs.begin();
    auto i1 = std::next(i0);
    const Node* px = nullptr;
    const Node* py = nullptr;
    if (i0->second == Rational(1) && i1->second == Rational(-1))
    {
      px = &i0->first;
      py = &i1->first;
    }
    else if (i0->second == Rational(-1) && i1->second == Rational(1))
    {
      px = &i1->first;
      py = &i0->first;
    }
    if (px != nullptr)
    {
      Rational v = -d.d_const;  // x - y >= -q
      auto key = std::make_pair(*px, *py);
      auto it = d_diff.find(key);
      if (it == d_diff.end() || v > it->second) d_diff[key] = v;
    }
  }
}

void IntOrderFacts::collectFacts(TNode a, bool negated)
{
  Kind k = a.getKind();
  if (k == Kind::NOT)
  {
    collectFacts(a[0], !negated);
    return;
  }
  if ((k == Kind::AND && !negated) || (k == Kind::OR && negated))
  {
    for (const Node& c : a)
    {
      collectFacts(c, negated);
    }
    return;
  }
  if (a.isClosure())
  {
    return;
  }
  Node l, r;
  bool strict = false;
  bool isEq = false;
  switch (k)
  {
    case Kind::GEQ: l = a[0]; r = a[1]; break;
    case Kind::GT: l = a[0]; r = a[1]; strict = true; break;
    case Kind::LEQ: l = a[1]; r = a[0]; break;
    case Kind::LT: l = a[1]; r = a[0]; strict = true; break;
    case Kind::EQUAL: l = a[0]; r = a[1]; isEq = true; break;
    default: return;
  }
  if (!l.getType().isInteger() || !r.getType().isInteger())
  {
    return;
  }
  Lin diff = linSub(toLin(l), toLin(r));
  if (isEq)
  {
    if (negated) return;  // a disequality gives no bound
    addGeq(diff);
    addGeq(linSub(toLin(r), toLin(l)));
    return;
  }
  if (!negated)
  {
    if (strict) diff.d_const -= Rational(1);
    addGeq(diff);
  }
  else
  {
    // not (l >= r) is r - l >= 1;  not (l > r) is r - l >= 0.  Integers.
    Lin rev = linSub(toLin(r), toLin(l));
    if (!strict) rev.d_const -= Rational(1);
    addGeq(rev);
  }
}

void IntOrderFacts::closeDiffs()
{
  std::vector<Node> atoms;
  std::map<Node, size_t> idx;
  for (const auto& [key, v] : d_diff)
  {
    for (const Node& n : {key.first, key.second})
    {
      if (idx.find(n) == idx.end())
      {
        idx[n] = atoms.size();
        atoms.push_back(n);
      }
    }
  }
  const size_t n = atoms.size();
  if (n == 0 || n > 48)
  {
    return;
  }
  const Rational negInf(Integer("-1000000000"));
  std::vector<std::vector<Rational>> best(n, std::vector<Rational>(n, negInf));
  for (size_t i = 0; i < n; ++i) best[i][i] = Rational(0);
  for (const auto& [key, v] : d_diff)
  {
    size_t i = idx[key.first], j = idx[key.second];
    if (v > best[i][j]) best[i][j] = v;
  }
  for (size_t m = 0; m < n; ++m)
  {
    for (size_t i = 0; i < n; ++i)
    {
      if (best[i][m] == negInf) continue;
      for (size_t j = 0; j < n; ++j)
      {
        if (best[m][j] == negInf) continue;
        Rational cand = best[i][m] + best[m][j];
        if (cand > best[i][j]) best[i][j] = cand;
      }
    }
  }
  for (size_t i = 0; i < n; ++i)
  {
    for (size_t j = 0; j < n; ++j)
    {
      if (i != j && best[i][j] != negInf)
      {
        d_diff[std::make_pair(atoms[i], atoms[j])] = best[i][j];
      }
    }
  }
}

bool IntOrderFacts::provNonNeg(const Lin& d) const
{
  if (d.d_coeffs.empty())
  {
    return d.d_const.sgn() >= 0;
  }
  // A stored many-variable fact `f >= 0` proves `d >= 0` whenever d - f is a
  // non-negative constant, i.e. d = f + c with c >= 0.
  for (const Lin& f : d_general)
  {
    if (f.d_coeffs.size() != d.d_coeffs.size()) continue;
    bool same = true;
    for (const auto& kv : d.d_coeffs)
    {
      auto it = f.d_coeffs.find(kv.first);
      if (it == f.d_coeffs.end() || it->second != kv.second)
      {
        same = false;
        break;
      }
    }
    if (same && (d.d_const - f.d_const).sgn() >= 0)
    {
      return true;
    }
  }
  if (d.d_coeffs.size() == 2)
  {
    auto i0 = d.d_coeffs.begin();
    auto i1 = std::next(i0);
    const Node* px = nullptr;
    const Node* py = nullptr;
    if (i0->second == Rational(1) && i1->second == Rational(-1))
    {
      px = &i0->first;
      py = &i1->first;
    }
    else if (i0->second == Rational(-1) && i1->second == Rational(1))
    {
      px = &i1->first;
      py = &i0->first;
    }
    if (px != nullptr)
    {
      auto it = d_diff.find(std::make_pair(*px, *py));
      if (it != d_diff.end() && (it->second + d.d_const).sgn() >= 0)
      {
        return true;
      }
    }
  }
  // Interval arithmetic: bound every monomial from below.
  Rational lo = d.d_const;
  for (const auto& [x, c] : d.d_coeffs)
  {
    if (c.sgn() > 0)
    {
      auto it = d_lb.find(x);
      if (it == d_lb.end()) return false;
      lo += c * it->second;
    }
    else
    {
      auto it = d_ub.find(x);
      if (it == d_ub.end()) return false;
      lo += c * it->second;
    }
  }
  return lo.sgn() >= 0;
}

void IntOrderFacts::harvest(const std::vector<Node>& assertions)
{
  for (const Node& a : assertions)
  {
    collectFacts(a, false);
  }
  closeDiffs();
}

bool IntOrderFacts::leq(TNode a, TNode b)
{
  if (a == b) return true;
  auto key = std::make_pair(Node(a), Node(b));
  auto it = d_leqCache.find(key);
  if (it != d_leqCache.end()) return it->second;
  bool res = provNonNeg(linSub(toLin(b), toLin(a)));
  d_leqCache[key] = res;
  return res;
}

bool IntOrderFacts::lt(TNode a, TNode b)
{
  // integers: a < b  iff  b - a - 1 >= 0
  Lin d = linSub(toLin(b), toLin(a));
  d.d_const -= Rational(1);
  return provNonNeg(d);
}

bool IntOrderFacts::nonNeg(TNode e) { return provNonNeg(toLin(e)); }

bool IntOrderFacts::geqConst(TNode e, const Rational& c)
{
  Lin d = toLin(e);
  d.d_const -= c;
  return provNonNeg(d);
}

void IntOrderFacts::strictUpperBoundsOf(TNode x, std::vector<Node>& out) const
{
  Node xn(x);
  for (const auto& [key, v] : d_diff)
  {
    if (key.second == xn && v.sgn() >= 1)
    {
      out.push_back(key.first);
    }
  }
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
