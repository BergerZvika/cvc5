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
 * Walk the post-translation assertions, count every Kind::EXP occurrence
 * (tree positions, not DAG nodes), and print a numbered report. The
 * numbering is stable for the lifetime of the pass, intended to be the
 * handle used by a future "rewrite instance N to <expr>" pass.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__EXP_ANALYZER_H
#define CVC5__PREPROCESSING__PASSES__EXP_ANALYZER_H

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class ExpAnalyzer : public PreprocessingPass
{
 public:
  ExpAnalyzer(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__EXP_ANALYZER_H */
