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
 * The arith-pow2-norm preprocessing pass.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__ARITH_POW2_NORM_H
#define CVC5__PREPROCESSING__PASSES__ARITH_POW2_NORM_H

#include <unordered_map>
#include <unordered_set>

#include "preprocessing/preprocessing_pass.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * Normalise the shift arithmetic that a PBV-to-int translation leaves behind,
 * so that bit-vector identities at a symbolic width k become syntactic, or
 * nearly so, instead of needing nonlinear search.
 *
 * A left shift is `(x * 2^e) mod 2^k` and a logical right shift `x div 2^e`.
 * cvc5 has no normal form relating two spellings of the same shift, so a
 * rewrite rule such as `(s >> a) >> b = (s >> b) >> a`, or `(s << a) << b` at
 * a shift amount past the width, reaches the nonlinear solver as two unrelated
 * terms and times out. Two equivalences, applied bottom-up to the rewriter's
 * polynomial normal form:
 *
 *   div-fuse  (x div p) div q  ->  x div (p*q)                 p, q > 0
 *   shl-past  in a dividend of `mod 2^K`, a monomial c * m * 2^e1 * ... * 2^en
 *             ->  ite(e1>=0 /\ ... /\ e1+...+en >= K, 0, monomial)     K >= 0
 *             and simply 0 when every ei >= 0 and e1+...+en-K >= 0 are
 *             provable (e.g. the monomial 2^K itself, or 2^K * 2^t).
 *
 * div-fuse is floor division with positive divisors. shl-past holds because
 * 2^K divides a monomial whose power-of-two exponents are non-negative and sum
 * to at least K. Positivity and non-negativity are proved from the term
 * structure and the top-level facts `x >= c` / `x = c`; nothing is assumed.
 *
 * Three further rules were tried and measured net-negative on sat25/rewrite
 * (a right shift past the width, stripping nested `mod 2^K`, and `y mod M ->
 * y` for y in range), so they are deliberately absent: each mostly traded a
 * dividend the solver sees is non-negative for one it cannot.
 *
 * Nothing is done under a quantifier.
 */
class ArithPow2Norm : public PreprocessingPass
{
 public:
  ArithPow2Norm(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /** Proved >= 0 from syntax and d_nonneg/d_pos facts. */
  bool nonneg(TNode n);
  /** Proved > 0 from syntax and facts. */
  bool pos(TNode n);
  /** Rebuild n bottom-up applying the rules. */
  Node normalize(TNode n);
  /** Apply the rules at the root of an already-normalized node. */
  Node applyRules(Node n);
  /** shl-past on a MOD whose modulus is 2^K. */
  Node shlPast(Node n);

  std::unordered_set<Node> d_nonnegVars;
  std::unordered_set<Node> d_posVars;
  std::unordered_map<Node, bool> d_nonnegCache;
  std::unordered_map<Node, bool> d_posCache;
  std::unordered_map<Node, Node> d_cache;

  struct Statistics
  {
    IntStat d_divFuse;
    IntStat d_shlPast;
    IntStat d_shlZero;
    Statistics(StatisticsRegistry& reg);
  };
  Statistics d_stats;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif
