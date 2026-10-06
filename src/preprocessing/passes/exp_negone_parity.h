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
 * Parity characterisation of powers of -1. Enabled by
 * --arith-exp-negone-parity.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__EXP_NEGONE_PARITY_H
#define CVC5__PREPROCESSING__PASSES__EXP_NEGONE_PARITY_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * For every distinct term `(exp -1 e)` in the assertions, add
 *
 *   ite(e mod 2 = 0, (exp -1 e) = 1, (exp -1 e) = -1)
 *
 * as a further assertion. This pins the VALUE of (-1)^e, where the existing
 * axioms only bound it: `neg-one` mirrors (exp -1 e) onto (exp -1 (- e)) and
 * the range axioms say it is non-zero, but nothing says WHICH of -1 and 1 it
 * is. A solver that then case-splits on `e mod 2` is left with an ordinary
 * polynomial problem in each branch.
 *
 * Sound for every integer exponent. For e >= 0 this is the definition of
 * (-1)^e; for e < 0, `**` gives 1 div (exp -1 (- e)), which is 1 div (+-1)
 * and so again +-1, and Euclidean `e mod 2` takes the same value at e and -e.
 *
 * Deliberately an ADDED ASSERTION rather than a rewrite of the term. Rewriting
 * `(exp -1 e)` to the ITE directly puts an ITE and a `mod` inside every
 * polynomial that mentions it -- one per occurrence rather than one per
 * distinct term -- and measurably loses: on the LoAT size0* families the
 * rewrite form solves nothing while this form solves most of them. Keeping the
 * term opaque leaves the polynomials' structure untouched and adds a single
 * Boolean split per distinct exponent.
 *
 * Nothing is added for a term under a quantifier, whose bound variables would
 * escape their binder.
 */
class ExpNegOneParity : public PreprocessingPass
{
 public:
  ExpNegOneParity(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif
