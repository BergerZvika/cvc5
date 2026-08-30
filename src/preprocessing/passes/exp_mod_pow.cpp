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
 * Implementation of the exp-mod-pow preprocessing pass.
 */

#include "preprocessing/passes/exp_mod_pow.h"

#include <vector>

#include "expr/node_algorithm.h"
#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

ExpModPow::ExpModPow(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "exp-mod-pow"),
      d_facts(preprocContext->getEnv())
{
}

bool ExpModPow::baseAtLeastTwo(TNode s)
{
  if (s.isConst())
  {
    return s.getConst<Rational>() >= Rational(2);
  }
  return d_facts.geqConst(s, Rational(2));
}

bool ExpModPow::isPositivePower(TNode d)
{
  // s^b with s >= 2 and b >= 0 is at least 1, so it is a safe `mod` divisor:
  // the result of a modulus by it is in [0, d) and in particular non-negative.
  if (d.isConst())
  {
    return d.getConst<Rational>().sgn() > 0;
  }
  return d.getKind() == Kind::EXP && baseAtLeastTwo(d[0]) && nonNeg(d[1]);
}

bool ExpModPow::nonNeg(TNode e)
{
  auto it = d_nonNeg.find(e);
  if (it != d_nonNeg.end())
  {
    return it->second;
  }
  // Insert a pessimistic answer first: it both terminates the recursion on a
  // cyclic-looking DAG walk and is the safe default if we bail out below.
  d_nonNeg[e] = false;
  bool res = false;
  switch (e.getKind())
  {
    case Kind::CONST_INTEGER:
    case Kind::CONST_RATIONAL: res = e.getConst<Rational>().sgn() >= 0; break;
    case Kind::EXP:
      // For s >= 2, s^t is >= 1 when t >= 0 and is `1 div s^|t|` = 0 when
      // t < 0, so it is non-negative for every exponent.
      res = baseAtLeastTwo(e[0]);
      break;
    case Kind::INTS_MODULUS:
    case Kind::INTS_MODULUS_TOTAL:
      // Euclidean remainder is in [0, |divisor|) whenever the divisor is
      // non-zero. (For a zero divisor cvc5 returns the dividend, whose sign we
      // do not know, hence the check.)
      res = isPositivePower(e[1]);
      break;
    case Kind::ADD:
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
    {
      res = true;
      for (const Node& c : e)
      {
        if (!nonNeg(c))
        {
          res = false;
          break;
        }
      }
      break;
    }
    default: res = d_facts.nonNeg(e); break;
  }
  if (!res)
  {
    // Structural analysis failed; the harvested assertions may still know.
    res = d_facts.nonNeg(e);
  }
  d_nonNeg[e] = res;
  return res;
}

ExpModPow::Order ExpModPow::compareExps(TNode a, TNode b)
{
  // Constants first: cheapest, and it covers the fully-concrete widths.
  if (a.isConst() && b.isConst())
  {
    const Rational& ra = a.getConst<Rational>();
    const Rational& rb = b.getConst<Rational>();
    d_numDecided++;
    return ra >= rb ? Order::GEQ : Order::LT;
  }
  if (a == b)
  {
    d_numDecided++;
    return Order::GEQ;
  }
  // Otherwise ask the order facts harvested from the assertions. On the
  // width-ordered problems -- where the input asserts p < q because a widening
  // extend says so -- this is exactly the comparison the rewrite needs, and
  // answering it here turns a case split into a decided branch.
  if (d_facts.leq(b, a))
  {
    d_numDecided++;
    return Order::GEQ;
  }
  if (d_facts.lt(a, b))
  {
    d_numDecided++;
    return Order::LT;
  }
  return Order::UNKNOWN;
}

Node ExpModPow::tryRules(TNode n)
{
  Kind k = n.getKind();
  if (k != Kind::INTS_MODULUS && k != Kind::INTS_MODULUS_TOTAL)
  {
    return Node::null();
  }
  TNode num = n[0];
  TNode den = n[1];
  // The divisor must be a power s^b of a base we know to be at least 2, with a
  // non-negative exponent.
  if (den.getKind() != Kind::EXP)
  {
    return Node::null();
  }
  TNode s = den[0];
  TNode b = den[1];
  if (!baseAtLeastTwo(s) || !nonNeg(b))
  {
    return Node::null();
  }

  NodeManager* nm = nodeManager();
  Node zero = nm->mkConstInt(Rational(0));

  // Rule 1: (mod (exp s a) (exp s b)) -> ite(a >= b, 0, (exp s a))
  if (num.getKind() == Kind::EXP && num[0] == s && nonNeg(num[1]))
  {
    Node a = num[1];
    d_numPow++;
    Order ord = compareExps(a, b);
    if (ord == Order::GEQ)
    {
      return zero;
    }
    if (ord == Order::LT)
    {
      return Node(num);
    }
    return nm->mkNode(
        Kind::ITE, nm->mkNode(Kind::GEQ, a, b), zero, Node(num));
  }

  // Rule 2: (mod (* x (exp s a)) (exp s b))
  //           -> ite(a >= b, 0, (* (mod x (exp s (- b a))) (exp s a)))
  //
  // Exactly one factor may be a power of s: with two of them the product is
  // s^(a1+a2) times the rest, which rule 2 would split at the wrong exponent.
  // Leaving that case to a later pass over the fused term is the conservative
  // choice.
  if (num.getKind() == Kind::MULT || num.getKind() == Kind::NONLINEAR_MULT)
  {
    Node pow;
    std::vector<Node> rest;
    for (const Node& f : num)
    {
      if (pow.isNull() && f.getKind() == Kind::EXP && f[0] == s
          && nonNeg(f[1]))
      {
        pow = f;
      }
      else
      {
        rest.push_back(f);
      }
    }
    if (!pow.isNull() && !rest.empty())
    {
      Node a = pow[1];
      d_numMult++;
      Order ord = compareExps(a, b);
      if (ord == Order::GEQ)
      {
        // s^b divides s^a divides x*s^a. Nothing else needs building -- in
        // particular not s^(b-a), whose exponent would be negative here.
        return zero;
      }
      Node x = rest.size() == 1 ? rest[0] : nm->mkNode(Kind::MULT, rest);
      // s^(b-a). Where a < b this exponent is at least 1 and the divisor at
      // least 2; when the order is unknown the guard below makes the a >= b
      // case unreachable, where it would otherwise be a negative exponent.
      Node gap = nm->mkNode(Kind::EXP, Node(s), nm->mkNode(Kind::SUB, b, a));
      // INTS_MODULUS_TOTAL for the introduced modulus: the divisor is
      // non-zero wherever this branch is reachable, so it agrees with the
      // partial operator there, and it carries no division-by-zero guard.
      Node inner = nm->mkNode(Kind::INTS_MODULUS_TOTAL, x, gap);
      Node body = nm->mkNode(Kind::MULT, inner, pow);
      if (ord == Order::LT)
      {
        return body;
      }
      return nm->mkNode(
          Kind::ITE, nm->mkNode(Kind::GEQ, a, b), zero, body);
    }
  }
  return Node::null();
}

Node ExpModPow::convert(TNode n)
{
  auto it = d_cache.find(n);
  if (it != d_cache.end())
  {
    return it->second;
  }
  // The side conditions are discharged from facts about free symbols, which
  // need not hold for a bound variable, so quantified bodies are left alone.
  if (n.isClosure())
  {
    d_cache[n] = n;
    return n;
  }
  Node ret;
  if (n.getNumChildren() == 0)
  {
    ret = n;
  }
  else
  {
    std::vector<Node> children;
    if (n.getMetaKind() == metakind::PARAMETERIZED)
    {
      children.push_back(n.getOperator());
    }
    bool changed = false;
    for (const Node& c : n)
    {
      Node cc = convert(c);
      changed = changed || cc != c;
      children.push_back(cc);
    }
    ret = changed ? nodeManager()->mkNode(n.getKind(), children) : Node(n);
    Node rw = tryRules(ret);
    if (!rw.isNull())
    {
      ret = rw;
    }
  }
  d_cache[n] = ret;
  return ret;
}

PreprocessingPassResult ExpModPow::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  const std::vector<Node>& assertions = assertionsToPreprocess->ref();
  d_facts.harvest(assertions);
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    Node before = assertions[i];
    Node after = convert(before);
    if (after != before)
    {
      assertionsToPreprocess->replace(i, rewrite(after));
    }
  }
  Trace("exp-mod-pow") << "ExpModPow: rewrote " << d_numPow
                       << " (mod pow pow) and " << d_numMult
                       << " (mod (* x pow) pow) terms, " << d_numDecided
                       << " of them with the exponent order entailed"
                       << std::endl;
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
