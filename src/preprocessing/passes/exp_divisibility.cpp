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
 * Implementation of the exp-divisibility preprocessing pass.
 */

#include "preprocessing/passes/exp_divisibility.h"

#include <vector>

#include "expr/node_algorithm.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "options/arith_options.h"
#include "util/integer.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

ExpDivisibility::ExpDivisibility(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "exp-divisibility")
{
}

PreprocessingPassResult ExpDivisibility::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager* nm = nodeManager();
  Node zero = nm->mkConstInt(Rational(0));
  uint64_t depth = options().arith.expDivisibilityDepth;
  if (depth == 0)
  {
    return PreprocessingPassResult::NO_CONFLICT;
  }

  // Collect the distinct (exp -1 e) terms, in order of first appearance.
  //
  // Deduplicating matters: the same exponent typically appears many times
  // over, and one assertion per distinct term is one Boolean split where one
  // per occurrence would be several. The ORDER matters too, and not only for
  // reproducibility -- the facts are logically identical either way, but they
  // are added in that order and so are decided in that order. Iterating an
  // unordered_set here cost 18 of the 109 hardest LoAT instances against
  // source order, purely from the search taking a different path.
  std::unordered_set<Node> seen;
  std::vector<Node> exps;
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
      if (cur.getKind() == Kind::EXP && seen.insert(cur).second)
      {
        exps.push_back(cur);
      }
      // push in reverse so children are visited left to right
      for (size_t i = 0, n = cur.getNumChildren(); i < n; ++i)
      {
        visit.push_back(cur[n - 1 - i]);
      }
    }
  }
  size_t added = 0;
  for (const Node& e : exps)
  {
    if (!e[0].isConst() || !e[0].getType().isInteger())
    {
      continue;
    }
    Rational rb = e[0].getConst<Rational>();
    if (!rb.isIntegral() || rb.getNumerator() < Integer(2))
    {
      continue;
    }
    // A bound variable in the exponent would escape its binder.
    if (expr::hasBoundVar(e))
    {
      continue;
    }
    Integer b = rb.getNumerator();
    Integer bj = b;
    for (uint64_t j = 1; j <= depth; ++j)
    {
      Node lem = nm->mkNode(
          Kind::IMPLIES,
          nm->mkNode(Kind::GEQ, e[1], nm->mkConstInt(Rational(Integer(j)))),
          nm->mkNode(Kind::EQUAL,
                     nm->mkNode(Kind::INTS_MODULUS_TOTAL,
                                e,
                                nm->mkConstInt(Rational(bj))),
                     zero));
      assertionsToPreprocess->push_back(rewrite(lem));
      added++;
      bj = bj * b;
    }
  }
  Trace("exp-divisibility")
      << "ExpDivisibility: added " << added << " divisibility facts"
      << std::endl;
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
