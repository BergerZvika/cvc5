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
 * n-fold same-base power fusion. Enabled by --arith-exp-pow-fuse.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__EXP_POW_FUSE_H
#define CVC5__PREPROCESSING__PASSES__EXP_POW_FUSE_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * Two identities over a constant base b >= 2, both UNGUARDED:
 *
 *   (P) a product with n identical factors (exp b t), 2 <= n <= N:
 *          (exp b t)^n = (exp b (n*t))
 *   (N) a nested power with a constant non-negative outer exponent c:
 *          (exp (exp b y) c) = (exp b (y*c))
 *
 * Neither needs a sign condition on the exponent, which is what makes them
 * different from the lemmas already present. `fuse` states
 * s1=s2 /\ t1>=0 /\ t2>=0 => exp(s1,t1)*exp(s2,t2) = exp(s1,t1+t2), and
 * `compose` states y>=0 /\ z>=0 => exp(exp(x,y),z) = exp(x,y*z). Both guards
 * are REQUIRED in general -- exp(b,1)*exp(b,-1) is 0 while exp(b,0) is 1 --
 * but both become vacuous in these two special cases:
 *
 *   equal exponents: for t < 0 every factor is `1 div b^|t|` = 0 for b >= 2,
 *   so the product is 0, and exp(b, n*t) with n*t < 0 is 0 as well. The two
 *   sides cannot disagree the way exp(b,1)*exp(b,-1) does, because the
 *   exponents cannot have opposite signs.
 *
 *   constant non-negative outer exponent: for y < 0 the inner power is 0, so
 *   the left side is 0^c, which is 0 for c >= 1; the right side has y*c < 0
 *   and is 0 too. For c = 0 both sides are 1.
 *
 * Verified exhaustively for b in [2,11], y in [-8,8], n in [1,5], c in [0,5].
 *
 * cvc5 derives the n = 2 and c = 2 cases on its own -- `unroll` turns a
 * constant square into a product and the pair lemmas reach it -- but not
 * n >= 3: `(** 2 y) * (** 2 y) * (** 2 y) = (** 2 (* 3 y))` does not close at
 * any timeout, and neither does the `(** (** 2 y) 3)` spelling. That is the
 * gap this pass fills; TPDB_ITS_Complexity/twn05.koat_2 is the motivating
 * benchmark, whose goal carries `(** (** 2 (+ it122 (- 1))) 2)`.
 *
 * (P) fires only on a product that ALREADY has n identical power factors, so
 * it introduces one term per shape actually present rather than enumerating
 * n. N caps the fold. Nothing is added under a quantifier.
 */
class ExpPowFuse : public PreprocessingPass
{
 public:
  ExpPowFuse(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif
