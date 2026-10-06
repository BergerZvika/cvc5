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
 * Ordering of equal-exponent powers by their bases. Enabled by
 * --arith-exp-base-order.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__EXP_BASE_ORDER_H
#define CVC5__PREPROCESSING__PASSES__EXP_BASE_ORDER_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * Relates the powers that share an exponent but differ in their base. For the
 * constant bases 2 <= b1 < b2 < ... occurring over one exponent `e`, add
 *
 *   e >= 0 => (exp b1 e) >= 1
 *   e >= 0 => (exp b2 e) >= (exp b1 e)     (consecutive pairs only)
 *
 * so the whole order follows transitively in linear rather than quadratic
 * size. Sound: for e >= 0 this is monotonicity of b |-> b^e on the positives.
 *
 * The powers are also CLOSED under the two ways an equal-exponent product
 * arises, since the base ordering is only useful once every power in the
 * constraint is one of the b_i:
 *
 *   e >= 0 => (exp a e) * (exp b e) = (exp (a*b) e)
 *   e >= 0 => (exp (exp a e) c)     = (exp (a^c) e)     (c a positive constant)
 *
 * Both introduce the fused power, which is the point -- `(2^e)^2` has to
 * become `4^e` before `16^e >= 4^e` can say anything about it. This is what
 * separates the pass from the existing --arith-exp-lemmas=fuse-base, which
 * states the same identity but only when the fused term ALREADY occurs, and
 * so never creates the term the ordering needs. Growth is bounded: one new
 * power per product, and none at all once the fused base exceeds d_baseCap.
 *
 * Which of the two forms the input presents depends on the rewrites in force
 * -- `(** (** 2 e) 2)` survives as a nested EXP by default but is unrolled
 * into a product by --arith-exp-rewrites=unroll -- so both are handled.
 *
 * Nothing is emitted for a term under a quantifier, whose bound variables
 * would escape their binder.
 */
class ExpBaseOrder : public PreprocessingPass
{
 public:
  ExpBaseOrder(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /** Largest exponent j admitted in a collapse b = a^j. */
  static const unsigned d_expCap = 64;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif
