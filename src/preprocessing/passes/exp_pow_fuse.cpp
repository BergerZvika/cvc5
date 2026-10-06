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
 * Implementation of the exp-pow-fuse preprocessing pass.
 */

#include "preprocessing/passes/exp_pow_fuse.h"

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

/** The base of `n` if it is a power over a constant integer base >= 2. */
bool constPowBase(const Node& n)
{
  if (n.getKind() != Kind::EXP || !n[0].isConst()
      || !n[0].getType().isInteger())
  {
    return false;
  }
  Rational rb = n[0].getConst<Rational>();
  return rb.isIntegral() && rb.getNumerator() >= Integer(2);
}

}  // namespace

ExpPowFuse::ExpPowFuse(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "exp-pow-fuse")
{
}

PreprocessingPassResult ExpPowFuse::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  uint64_t maxFold = options().arith.expPowFuse;
  if (maxFold < 2)
  {
    return PreprocessingPassResult::NO_CONFLICT;
  }
  NodeManager* nm = nodeManager();

  // Source order, for the same reason as the other exp passes: the facts are
  // logically the same in any order but are decided in the order asserted.
  std::unordered_set<Node> seen;
  std::vector<Node> lemmas;

  auto addLemma = [&](const Node& lhs, const Node& b, const Node& e) {
    Node rhs = nm->mkNode(Kind::EXP, b, e);
    Node lem = rewrite(nm->mkNode(Kind::EQUAL, lhs, rhs));
    if (lem.isConst() || !seen.insert(lem).second)
    {
      return;
    }
    lemmas.push_back(lem);
  };

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
        // (N) nested power with a constant non-negative outer exponent.
        if (cur.getKind() == Kind::EXP && constPowBase(cur[0])
            && cur[1].isConst() && cur[1].getType().isInteger())
        {
          Rational rc = cur[1].getConst<Rational>();
          if (rc.isIntegral() && rc.getNumerator().sgn() >= 0)
          {
            Node inner = cur[0];
            addLemma(cur,
                     inner[0],
                     nm->mkNode(Kind::MULT, inner[1], cur[1]));
          }
        }
        // (P) a product with n identical constant-base power factors.
        if (cur.getKind() == Kind::MULT || cur.getKind() == Kind::NONLINEAR_MULT)
        {
          std::map<Node, uint64_t> cnt;
          for (const Node& c : cur)
          {
            if (constPowBase(c))
            {
              cnt[c]++;
            }
          }
          for (const std::pair<const Node, uint64_t>& kv : cnt)
          {
            if (kv.second < 2)
            {
              continue;
            }
            uint64_t n = std::min<uint64_t>(kv.second, maxFold);
            std::vector<Node> factors(n, kv.first);
            Node lhs = nm->mkNode(Kind::MULT, factors);
            Node e = nm->mkNode(
                Kind::MULT,
                nm->mkConstInt(Rational(Integer(static_cast<uint64_t>(n)))),
                kv.first[1]);
            addLemma(lhs, kv.first[0], e);
          }
        }
      }
      for (size_t i = 0, m = cur.getNumChildren(); i < m; ++i)
      {
        visit.push_back(cur[m - 1 - i]);
      }
    }
  }
  for (const Node& l : lemmas)
  {
    assertionsToPreprocess->push_back(l);
  }
  Trace("exp-pow-fuse") << "ExpPowFuse: added " << lemmas.size() << " lemmas"
                        << std::endl;
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
