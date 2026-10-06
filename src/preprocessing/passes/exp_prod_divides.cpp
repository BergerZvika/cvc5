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
 * Implementation of the exp-prod-divides preprocessing pass.
 */

#include "preprocessing/passes/exp_prod_divides.h"

#include <map>
#include <vector>

#include "expr/node_algorithm.h"
#include "options/arith_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "util/integer.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

namespace {

/**
 * The base of `n` if it is a power over a constant integer base >= 2, and a
 * null node otherwise. A symbolic base is skipped rather than guarded: the
 * guard would have to be `b >= 2`, and every benchmark this pass is aimed at
 * has the literal base 2.
 */
Node constPowBase(const Node& n)
{
  if (n.getKind() != Kind::EXP || !n[0].isConst()
      || !n[0].getType().isInteger())
  {
    return Node::null();
  }
  Rational rb = n[0].getConst<Rational>();
  if (!rb.isIntegral() || rb.getNumerator() < Integer(2))
  {
    return Node::null();
  }
  return n[0];
}

}  // namespace

ExpProdDivides::ExpProdDivides(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "exp-prod-divides")
{
}

PreprocessingPassResult ExpProdDivides::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  uint64_t budget = options().arith.expProdDivides;
  if (budget == 0)
  {
    return PreprocessingPassResult::NO_CONFLICT;
  }
  NodeManager* nm = nodeManager();
  Node zero = nm->mkConstInt(Rational(0));

  // Distinct power terms and distinct products with a power factor, both in
  // order of first appearance. Source order matters for the same reason it
  // does in ExpDivisibility: the facts are logically the same in any order,
  // but they are asserted in this order and so decided in this order.
  std::unordered_set<Node> seenPow;
  std::unordered_set<Node> seenProd;
  std::vector<Node> pows;
  std::vector<Node> prods;
  for (const Node& a : assertionsToPreprocess->ref())
  {
    std::vector<Node> visit{a};
    std::unordered_set<Node> visited;
    while (!visit.empty())
    {
      Node cur = visit.back();
      visit.pop_back();
      if (!visited.insert(cur).second)
      {
        continue;
      }
      // A bound variable in the term would escape its binder.
      if (!expr::hasBoundVar(cur))
      {
        if (!constPowBase(cur).isNull())
        {
          if (seenPow.insert(cur).second)
          {
            pows.push_back(cur);
          }
        }
        else if (cur.getKind() == Kind::MULT || cur.getKind() == Kind::NONLINEAR_MULT)
        {
          for (const Node& c : cur)
          {
            if (!constPowBase(c).isNull())
            {
              if (seenProd.insert(cur).second)
              {
                prods.push_back(cur);
              }
              break;
            }
          }
        }
      }
      // push in reverse so children are visited left to right
      for (size_t i = 0, n = cur.getNumChildren(); i < n; ++i)
      {
        visit.push_back(cur[n - 1 - i]);
      }
    }
  }
  if (pows.empty() || prods.empty())
  {
    return PreprocessingPassResult::NO_CONFLICT;
  }

  // The divisor candidates, grouped by base.
  std::map<Node, std::vector<Node>> byBase;
  for (const Node& p : pows)
  {
    byBase[constPowBase(p)].push_back(p);
  }

  size_t added = 0;
  for (const Node& m : prods)
  {
    // The exponents of m's power factors, per base. A product may mix bases;
    // each base is handled on its own, with the other bases' factors counted
    // as part of the opaque remaining coefficient.
    std::map<Node, std::vector<Node>> expsOf;
    for (const Node& c : m)
    {
      Node b = constPowBase(c);
      if (!b.isNull())
      {
        expsOf[b].push_back(c[1]);
      }
    }
    for (const std::pair<const Node, std::vector<Node>>& be : expsOf)
    {
      const std::vector<Node>& es = be.second;
      Node sum = es.size() == 1 ? es[0] : nm->mkNode(Kind::ADD, es);
      // Only a COMPOUND exponent is worth stating this about. When the
      // exponent is a bare variable -- the `2^k`, `2^m` of an ordinary width
      // -- the fact is either trivial or already available: the PBV width
      // machinery emits the pure split `2^m = 2^k * 2^(m-k)` for those pairs
      // itself. The case that needs this pass is a shift composed out of
      // several amounts, whose exponent is a sum or, once the translation has
      // wrapped it in its modular reduction, a `mod_total` over one -- so the
      // test is for any non-atomic exponent rather than for ADD specifically.
      // Without the restriction the pass fires everywhere and is a net loss
      // on Alive (169 -> 164 at 20s), gaining the shift benchmark but
      // perturbing seven others that the base configuration already solves.
      if (sum.getNumChildren() == 0)
      {
        continue;
      }
      for (const Node& d : byBase[be.first])
      {
        if (added >= budget)
        {
          break;
        }
        // d itself being one of m's factors makes the lemma trivial.
        if (d == m)
        {
          continue;
        }
        Node guard = nm->mkNode(Kind::AND,
                                nm->mkNode(Kind::GEQ, d[1], zero),
                                nm->mkNode(Kind::GEQ, sum, d[1]));
        // Stated as `M mod d = 0` rather than with a skolem witness
        // `M = d * w`. Both are the same fact and both close the motivating
        // benchmark, but the witness form introduces a fresh unconstrained
        // integer per lemma, and on Alive that cost five benchmarks that the
        // base configuration solves in under 9s -- AndOrXor_516/530/698/2494
        // and Select_575a -- while gaining nothing the mod form does not.
        // The divisor is nonzero under the guard (b >= 2, u >= 0 give
        // d >= 1), so the totalised modulus is the ordinary one here.
        Node lem = nm->mkNode(
            Kind::IMPLIES,
            guard,
            nm->mkNode(Kind::EQUAL,
                       nm->mkNode(Kind::INTS_MODULUS_TOTAL, m, d),
                       zero));
        assertionsToPreprocess->push_back(rewrite(lem));
        added++;
      }
    }
  }
  Trace("exp-prod-divides")
      << "ExpProdDivides: added " << added << " divisibility facts over "
      << prods.size() << " products and " << pows.size() << " powers"
      << std::endl;
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
