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
 * Instances of unsigned-division identities for PBV terms. Enabled by
 * --pbv-div-lemmas.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__PBV_DIV_LEMMAS_H
#define CVC5__PREPROCESSING__PASSES__PBV_DIV_LEMMAS_H

#include "preprocessing/preprocessing_pass.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * Add instances of two floor-division identities, at the PBV level and
 * before int-blasting:
 *
 *   (D1)  nooverflow(a, b) & a != 0 & b != 0
 *             ->  (x / a) / b = x / (a * b)
 *   (D2)  nooverflow(x, a) & c urem a = 0 & c != 0
 *             ->  (x * a) / c = x / (c / a)
 *
 * where `/` is pbvudiv and nooverflow(p, q) is the product's high half being
 * zero, `extract(zext(p) * zext(q), 2w-1, w) = 0`, the form compiler
 * preconditions state it in. Both are valid for every width (D2: c = a*q
 * exactly and a != 0, so floor(x*a / (a*q)) = floor(x/q)). After
 * int-blasting each is an identity about floor division of products that the
 * nonlinear solver does not find by itself, which leaves a goal like
 * `(x / a) / b != x / (a * b)` open for ever.
 *
 * An instance is added only when both sides of its conclusion already occur
 * in the assertions, so the pass introduces no new division terms.
 */
class PbvDivLemmas : public PreprocessingPass
{
 public:
  PbvDivLemmas(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  struct Statistics
  {
    /** Instances of (D1) added. */
    IntStat d_numNested;
    /** Instances of (D2) added. */
    IntStat d_numCancel;
    Statistics(StatisticsRegistry& reg);
  };
  Statistics d_stats;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif
