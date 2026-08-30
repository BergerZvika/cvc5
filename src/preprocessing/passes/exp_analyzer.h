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

  /**
   * --analyze-exp-instances=multiply-only-{l3,l4,relate,l3-common,
   * l3-common-l4}: assert L3/L4 relational lemmas between same-base powers
   * whose exponent gap is symbolic (so multiply-only could not fold them).
   * doL3/doL4 select the lemmas; l3Common restricts each upper power to a
   * single lower pivot, in which case L4 (if enabled) is emitted for that same
   * pair. See the .cpp for the exact conditions.
   */
  void addRelationalLemmas(AssertionPipeline* assertionsToPreprocess,
                           bool report,
                           bool doL3,
                           bool doL4,
                           bool l3Common);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__EXP_ANALYZER_H */
