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
 * Symbolic-modulus divisibility for products containing a constant-base
 * power. Enabled by --arith-exp-prod-divides.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__EXP_PROD_DIVIDES_H
#define CVC5__PREPROCESSING__PASSES__EXP_PROD_DIVIDES_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * For every product `M` in the problem that has one or more `(exp b t_i)`
 * factors sharing a constant base b >= 2, and every distinct `(exp b u)` term
 * over the same base, add
 *
 *   u >= 0 /\ (t_1 + ... + t_n) >= u  =>  M mod (exp b u) = 0
 *
 * which is what the surrounding `x = q * 2^k + r, 0 <= r < 2^k` encoding
 * needs to conclude r = 0.
 *
 * Sound for every integer exponent. If some t_i < 0 then `(exp b t_i)` is
 * `1 div b^|t_i|`, which is 0 for b >= 2, so M is 0 and every modulus divides
 * it. If every t_i >= 0 then M = e * b^(t_1+...+t_n) with e the remaining
 * factors, and b^T = b^u * b^(T-u) whenever T >= u >= 0, so b^u divides M
 * whatever the sign of e. The divisor is at least 1 under the guard, so the
 * totalised modulus is the ordinary one.
 *
 * The equivalent skolem-witness spelling `M = (exp b u) * w` closes the same
 * benchmarks but introduces a fresh unconstrained integer per lemma, which
 * measured five losses on Alive (AndOrXor_516/530/698/2494, Select_575a, all
 * solved in under 9s without this pass) for no additional gain.
 *
 * This is the SYMBOLIC-modulus counterpart of --arith-exp-divisibility, whose
 * moduli are the constants b^1..b^N. cvc5 cannot derive either on its own:
 * `c >= k >= 1 /\ 2^k does not divide 2^c` does not close. But stating only
 * the pure power split `2^c = 2^k * 2^(c-k)`, with or without the new term,
 * is NOT enough for the PBV shift benchmarks -- the solver will not multiply
 * that equation through by the shifted value. The fact has to be stated about
 * the PRODUCT, which is what this pass does and what
 * --arith-exp-divisibility does not.
 *
 * The motivating shape is a left shift past the width in the PBV-to-int
 * encoding: `(pbvshl (pbvshl X C1) C2)` becomes `X * 2^(C1+C2) - q * 2^k`
 * with `0 <= that < 2^k`, and the proof that it is 0 when C1 + C2 >= k needs
 * `2^k | X * 2^(C1+C2)`. Alive/InstCombineShift228 is the smallest example.
 *
 * N caps the number of lemmas, since the pair count is quadratic in the
 * number of power terms; pairs are taken in source order. Nothing is added
 * for a term under a quantifier, whose bound variables would escape their
 * binder.
 */
class ExpProdDivides : public PreprocessingPass
{
 public:
  ExpProdDivides(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif
