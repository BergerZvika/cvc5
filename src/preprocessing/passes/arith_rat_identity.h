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
 * Denominator clearing for arithmetic equalities. Enabled by
 * --arith-rat-identity.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__ARITH_RAT_IDENTITY_H
#define CVC5__PREPROCESSING__PASSES__ARITH_RAT_IDENTITY_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * For every arithmetic equality L = R that contains a real division or powers
 * of one base whose exponents differ by a constant, assert the valid formula
 *
 *   G => (L = R  <=>  N = 0)
 *
 * where N / D is L - R brought over a common denominator, and G collects the
 * side conditions: every divisor is non-zero, and for each group of powers
 * exp(s, e + c_1), ..., exp(s, e + c_k) with c_min = min c_i, e + c_min >= 0.
 * Under that guard exp(s, e + c_i) is replaced by s^(c_i - c_min) *
 * exp(s, e + c_min), so the group shares a single power.
 *
 * N is a polynomial, and the rewriter expands it into its normal form. When
 * L = R is an identity of rational functions -- the shape of a verified
 * recurrence solution -- N normalizes to 0 and the lemma reduces to G => L = R,
 * which leaves the solver only the guard to refute instead of a nonlinear
 * problem over the purified reciprocals.
 *
 * Nothing is emitted for a term under a quantifier.
 */
class ArithRatIdentity : public PreprocessingPass
{
 public:
  ArithRatIdentity(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /** Largest constant exponent gap c_i - c_min that is expanded. */
  static const unsigned d_shiftCap = 16;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif
