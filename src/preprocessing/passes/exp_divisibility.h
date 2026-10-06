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
 * Dyadic divisibility facts for constant-base powers. Enabled by
 * --arith-exp-divisibility.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__EXP_DIVISIBILITY_H
#define CVC5__PREPROCESSING__PASSES__EXP_DIVISIBILITY_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * For every distinct term `(exp b e)` with a constant base b >= 2, add
 *
 *   e >= j  =>  (exp b e) mod b^j = 0        for j = 1 .. N
 *
 * where N is --arith-exp-divisibility. Sound because b^j divides b^e as soon
 * as e >= j, and each modulus is a CONSTANT, so a conjunct is linear in the
 * power term and introduces no new term.
 *
 * cvc5 gets j=1 for free -- `2 | 2^k` for k >= 1 falls out of the parity
 * reasoning already present -- but not j >= 2: it does not close
 * `k >= 2 /\ 2^k mod 4 != 0` at all. That gap is what blocks the finite-bit
 * refutations of the width-parametric PBV lemmas: their arguments run
 * `t = x*s mod 2^k`, and pushing that down to `t mod 4 = (x*s) mod 4` needs
 * exactly `4 | 2^k`. sat25/lemmas/lemma_MUL_REF15_bw_k is the smallest
 * example, refuted by a mod-2 then mod-4 case split once the fact is present.
 *
 * Deliberately a PREPROCESSING pass rather than an ExpSolver initial-refine
 * lemma, though the facts are identical. Emitted from the nl-ext loop they
 * only reach the solver after a full linear model has been built, by which
 * point the search has already committed; stated up front they are available
 * to the linear solver from the first round. Measured on sat25/lemmas: the
 * init-refine placement leaves lemma_MUL_REF15_bw_k unsolved at every depth,
 * this one closes it.
 *
 * Nothing is added for a term under a quantifier, whose bound variables would
 * escape their binder.
 */
class ExpDivisibility : public PreprocessingPass
{
 public:
  ExpDivisibility(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif
