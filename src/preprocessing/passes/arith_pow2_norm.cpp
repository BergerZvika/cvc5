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
 * Implementation of the arith-pow2-norm preprocessing pass.
 */

#include "preprocessing/passes/arith_pow2_norm.h"

#include <vector>

#include "expr/node_algorithm.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "util/rational.h"
#include "util/statistics_registry.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

namespace {

bool isMod(Kind k)
{
  return k == Kind::INTS_MODULUS || k == Kind::INTS_MODULUS_TOTAL;
}

bool isDiv(Kind k)
{
  return k == Kind::INTS_DIVISION || k == Kind::INTS_DIVISION_TOTAL;
}

bool isMult(Kind k) { return k == Kind::MULT || k == Kind::NONLINEAR_MULT; }

/** (exp 2 e) */
bool isPow2(TNode n)
{
  return n.getKind() == Kind::EXP && n[0].isConst()
         && n[0].getConst<Rational>() == Rational(2);
}

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

bool isIntVar(TNode n) { return n.isVar() && n.getType().isInteger(); }

}  // namespace

ArithPow2Norm::ArithPow2Norm(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "arith-pow2-norm"),
      d_stats(statisticsRegistry())
{
}

ArithPow2Norm::Statistics::Statistics(StatisticsRegistry& reg)
    : d_divFuse(reg.registerInt("preprocessing::passes::ArithPow2Norm::DivFuse")),
      d_shlPast(reg.registerInt("preprocessing::passes::ArithPow2Norm::ShlPast")),
      d_shlZero(reg.registerInt("preprocessing::passes::ArithPow2Norm::ShlZero"))
{
}

bool ArithPow2Norm::nonneg(TNode n)
{
  auto it = d_nonnegCache.find(n);
  if (it != d_nonnegCache.end())
  {
    return it->second;
  }
  bool res = false;
  Kind k = n.getKind();
  if (n.isConst())
  {
    res = n.getType().isRealOrInt() && n.getConst<Rational>().sgn() >= 0;
  }
  else if (isIntVar(n))
  {
    res = d_nonnegVars.find(n) != d_nonnegVars.end();
  }
  else if (isPow2(n))
  {
    // 2^e is 2^e >= 1 for e >= 0 and 0 for e < 0 under '**'
    res = true;
  }
  else if (isMod(k))
  {
    // a mod by 0 is uninterpreted, anything else lands in [0,|m|)
    res = pos(n[1]);
  }
  else if (isDiv(k))
  {
    res = pos(n[1]) && nonneg(n[0]);
  }
  else if (k == Kind::ADD || isMult(k))
  {
    res = true;
    for (const Node& c : n)
    {
      if (!nonneg(c))
      {
        res = false;
        break;
      }
    }
  }
  else if (k == Kind::ITE)
  {
    res = nonneg(n[1]) && nonneg(n[2]);
  }
  d_nonnegCache[n] = res;
  return res;
}

bool ArithPow2Norm::pos(TNode n)
{
  auto it = d_posCache.find(n);
  if (it != d_posCache.end())
  {
    return it->second;
  }
  bool res = false;
  Kind k = n.getKind();
  if (n.isConst())
  {
    res = n.getType().isRealOrInt() && n.getConst<Rational>().sgn() > 0;
  }
  else if (isIntVar(n))
  {
    res = d_posVars.find(n) != d_posVars.end();
  }
  else if (isPow2(n))
  {
    res = nonneg(n[1]);
  }
  else if (isMult(k))
  {
    res = true;
    for (const Node& c : n)
    {
      if (!pos(c))
      {
        res = false;
        break;
      }
    }
  }
  else if (k == Kind::ADD)
  {
    bool anyPos = false;
    res = true;
    for (const Node& c : n)
    {
      if (!nonneg(c))
      {
        res = false;
        break;
      }
      anyPos = anyPos || pos(c);
    }
    res = res && anyPos;
  }
  else if (k == Kind::ITE)
  {
    res = pos(n[1]) && pos(n[2]);
  }
  d_posCache[n] = res;
  return res;
}

Node ArithPow2Norm::shlPast(Node n)
{
  NodeManager* nm = nodeManager();
  Node zero = nm->mkConstInt(Rational(0));
  Node m = n[1];
  Node kk = m[1];
  std::vector<Node> monos;
  if (n[0].getKind() == Kind::ADD)
  {
    monos.insert(monos.end(), n[0].begin(), n[0].end());
  }
  else
  {
    monos.push_back(n[0]);
  }
  bool changed = false;
  for (Node& mono : monos)
  {
    std::vector<Node> exps;
    if (isPow2(mono))
    {
      exps.push_back(mono[1]);
    }
    else if (isMult(mono.getKind()))
    {
      for (const Node& f : mono)
      {
        if (isPow2(f))
        {
          exps.push_back(f[1]);
        }
      }
    }
    if (exps.empty())
    {
      continue;
    }
    Node sum = exps.size() == 1 ? exps[0] : nm->mkNode(Kind::ADD, exps);
    std::vector<Node> cond;
    for (const Node& e : exps)
    {
      if (!nonneg(e))
      {
        cond.push_back(nm->mkNode(Kind::GEQ, e, zero));
      }
    }
    Node diff = rewrite(nm->mkNode(Kind::SUB, sum, kk));
    if (cond.empty() && nonneg(diff))
    {
      // 2^K provably divides the monomial
      mono = zero;
      ++d_stats.d_shlZero;
      changed = true;
      continue;
    }
    cond.push_back(nm->mkNode(Kind::GEQ, sum, kk));
    Node c = cond.size() == 1 ? cond[0] : nm->mkNode(Kind::AND, cond);
    mono = nm->mkNode(Kind::ITE, c, zero, mono);
    ++d_stats.d_shlPast;
    changed = true;
  }
  if (!changed)
  {
    return n;
  }
  Node sum = monos.size() == 1 ? monos[0] : nm->mkNode(Kind::ADD, monos);
  return nm->mkNode(n.getKind(), sum, m);
}

Node ArithPow2Norm::applyRules(Node n)
{
  NodeManager* nm = nodeManager();
  // div-fuse, repeatedly: a chain of right shifts collapses to one division
  while (isDiv(n.getKind()) && isDiv(n[0].getKind()) && pos(n[1])
         && pos(n[0][1]))
  {
    // floor(floor(x/p)/q) = floor(x/(p*q)) for p,q > 0
    n = rewrite(nm->mkNode(n.getKind(),
                           n[0][0],
                           nm->mkNode(Kind::NONLINEAR_MULT, n[0][1], n[1])));
    ++d_stats.d_divFuse;
  }
  if (isMod(n.getKind()) && isPow2(n[1]) && nonneg(n[1][1]))
  {
    Node r = shlPast(n);
    if (r != n)
    {
      return rewrite(r);
    }
  }
  return n;
}

Node ArithPow2Norm::normalize(TNode n)
{
  auto it = d_cache.find(n);
  if (it != d_cache.end())
  {
    return it->second;
  }
  Node res = n;
  if (n.getNumChildren() > 0 && !n.isClosure())
  {
    bool changed = false;
    std::vector<Node> ch;
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      ch.push_back(n.getOperator());
    }
    for (const Node& c : n)
    {
      Node nc = normalize(c);
      changed = changed || nc != c;
      ch.push_back(nc);
    }
    if (changed)
    {
      res = nodeManager()->mkNode(n.getKind(), ch);
      if (res.getType().isInteger())
      {
        res = rewrite(res);
      }
    }
    Kind k = res.getKind();
    if (isMod(k) || isDiv(k))
    {
      res = applyRules(res);
    }
  }
  d_cache[n] = res;
  return res;
}

PreprocessingPassResult ArithPow2Norm::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  AssertionPipeline* ap = assertionsToPreprocess;
  // Bound facts from the top-level conjuncts.
  std::vector<Node> cs;
  for (size_t i = 0, n = ap->size(); i < n; ++i)
  {
    collectConjuncts((*ap)[i], cs);
  }
  for (const Node& c : cs)
  {
    if (c.getKind() == Kind::GEQ && isIntVar(c[0]) && c[1].isConst())
    {
      int s = c[1].getConst<Rational>().sgn();
      if (s >= 0)
      {
        d_nonnegVars.insert(c[0]);
      }
      if (s > 0)
      {
        d_posVars.insert(c[0]);
      }
    }
    else if (c.getKind() == Kind::EQUAL && isIntVar(c[0]) && c[1].isConst()
             && c[1].getType().isInteger())
    {
      int s = c[1].getConst<Rational>().sgn();
      if (s >= 0)
      {
        d_nonnegVars.insert(c[0]);
      }
      if (s > 0)
      {
        d_posVars.insert(c[0]);
      }
    }
  }
  for (size_t i = 0, n = ap->size(); i < n; ++i)
  {
    Node a = (*ap)[i];
    if (expr::hasBoundVar(a))
    {
      continue;
    }
    Node na = normalize(a);
    if (na != a)
    {
      ap->replace(i, rewrite(na));
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
