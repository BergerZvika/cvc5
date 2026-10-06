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
 * Implementation of the exp-base-order preprocessing pass.
 */

#include "preprocessing/passes/exp_base_order.h"

#include <algorithm>
#include <map>
#include <vector>

#include "expr/node_algorithm.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

namespace {

/** The base of `n` if it is a power with a constant integer base >= 2. */
bool constBase(TNode n, Integer& base)
{
  if (n.getKind() != Kind::EXP || !n[0].isConst()
      || !n[0].getType().isInteger())
  {
    return false;
  }
  const Rational& r = n[0].getConst<Rational>();
  if (!r.isIntegral())
  {
    return false;
  }
  base = r.getNumerator();
  return base >= Integer(2);
}

}  // namespace

ExpBaseOrder::ExpBaseOrder(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "exp-base-order")
{
}

PreprocessingPassResult ExpBaseOrder::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager* nm = nodeManager();
  Node zero = nm->mkConstInt(Rational(0));
  Node one = nm->mkConstInt(Rational(1));

  // exponent -> bases seen over it. The exponents are kept in order of first
  // appearance rather than iterated out of a hash table: the facts are
  // logically the same either way, but they are ASSERTED in this order and so
  // decided in this order, and that is worth several instances on this corpus
  // (the same effect exp-negone-parity records).
  std::vector<Node> expOrder;
  std::map<Node, std::vector<Integer>> bases;
  std::vector<Node> lemmas;

  auto note = [&](const Node& e, const Integer& b) {
    std::map<Node, std::vector<Integer>>::iterator it = bases.find(e);
    if (it == bases.end())
    {
      expOrder.push_back(e);
      bases[e].push_back(b);
      return;
    }
    if (std::find(it->second.begin(), it->second.end(), b) == it->second.end())
    {
      it->second.push_back(b);
    }
  };
  auto guard = [&](const Node& e, const Node& body) {
    return nm->mkNode(Kind::IMPLIES, nm->mkNode(Kind::GEQ, e, zero), body);
  };
  auto power = [&](const Integer& b, const Node& e) {
    return nm->mkNode(Kind::EXP, nm->mkConstInt(Rational(b)), e);
  };
  // `t` repeated `j` times as a product.
  auto repeat = [&](const Node& t, uint32_t j) {
    std::vector<Node> fs(j, t);
    return j == 1 ? t : nm->mkNode(Kind::MULT, fs);
  };

  std::unordered_set<TNode> visited;
  for (const Node& a : assertionsToPreprocess->ref())
  {
    std::vector<TNode> visit{a};
    while (!visit.empty())
    {
      TNode cur = visit.back();
      visit.pop_back();
      if (!visited.insert(cur).second)
      {
        continue;
      }
      for (size_t i = 0, n = cur.getNumChildren(); i < n; ++i)
      {
        visit.push_back(cur[n - 1 - i]);
      }
      if (cur.getKind() != Kind::EXP || expr::hasBoundVar(cur))
      {
        continue;
      }
      Integer b;
      if (constBase(cur, b))
      {
        note(cur[1], b);
        continue;
      }
      // `(exp (exp a e) c)` for a positive constant c: state it as the
      // c-fold product of the inner power, which introduces no new base.
      // Only reachable while the outer power is still an EXP node, i.e. when
      // --arith-exp-rewrites=unroll has not already done exactly this.
      if (!cur[1].isConst() || !cur[1].getType().isInteger()
          || !constBase(cur[0], b))
      {
        continue;
      }
      const Rational& rc = cur[1].getConst<Rational>();
      if (!rc.isIntegral() || rc.getNumerator().sgn() <= 0
          || rc.getNumerator() > Integer(d_expCap))
      {
        continue;
      }
      uint32_t c = rc.getNumerator().toUnsignedInt();
      lemmas.push_back(guard(cur[0][1], cur.eqNode(repeat(cur[0], c))));
      note(cur[0][1], b);
    }
  }

  size_t ncollapse = 0, nord = 0;
  for (const Node& e : expOrder)
  {
    std::vector<Integer>& bs = bases[e];
    std::sort(bs.begin(), bs.end());

    // COLLAPSE. Whenever one base is a perfect power of a smaller one in the
    // same group, b = a^j, then b^e = (a^e)^j -- so the two are not merely
    // ordered, they are the same quantity, and every power in the group that
    // shares a root collapses onto a single term. This is far stronger than
    // the order, and on twn09.koat_2 it is the difference between a 38 s
    // refutation and a 1.6 s one: with `16^e = (2^e)^4` the constraint becomes
    // a polynomial in one power instead of a relation between three.
    for (size_t i = 0, n = bs.size(); i < n; ++i)
    {
      for (size_t k = 0; k < i; ++k)
      {
        Integer acc = bs[k];
        uint32_t j = 1;
        while (acc < bs[i] && j < d_expCap)
        {
          acc = acc * bs[k];
          ++j;
        }
        if (acc == bs[i] && j >= 2)
        {
          lemmas.push_back(
              guard(e, power(bs[i], e).eqNode(repeat(power(bs[k], e), j))));
          ++ncollapse;
          break;  // the smallest such root is enough
        }
      }
    }

    // ORDER. Consecutive pairs only, so the whole order follows transitively
    // in linear rather than quadratic size.
    lemmas.push_back(guard(e, nm->mkNode(Kind::GEQ, power(bs[0], e), one)));
    for (size_t i = 1, n = bs.size(); i < n; ++i)
    {
      lemmas.push_back(guard(
          e, nm->mkNode(Kind::GEQ, power(bs[i], e), power(bs[i - 1], e))));
      ++nord;
    }
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
  Trace("exp-base-order") << "ExpBaseOrder: " << expOrder.size()
                          << " exponent groups, " << ncollapse
                          << " collapses, " << nord << " orderings"
                          << std::endl;
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
