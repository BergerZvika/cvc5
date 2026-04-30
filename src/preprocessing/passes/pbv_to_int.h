/******************************************************************************
 * Top contributors (to current version):
 *   Zvika Berger
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The pbv-to-int preprocessing pass.
 */

#ifndef __CVC5__PREPROCESSING__PASSES__PBV_TO_INT_H
#define __CVC5__PREPROCESSING__PASSES__PBV_TO_INT_H

#include "context/cdhashmap.h"
#include "context/cdo.h"
#include "context/context.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/pbv/int_blaster.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using CDNodeMap = context::CDHashMap<Node, Node>;

class PBVToInt : public PreprocessingPass
{
 public:
  PBVToInt(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

  // Push range/well-formedness lemmas produced by the int-blaster into the
  // assertion pipeline so the int-encoded problem stays equisatisfiable.
  void addFinalizeAssertions(
      AssertionPipeline* assertionsToPreprocess,
      const std::vector<TrustNode>& additionalConstraints);

  // Register `pbvVar -> INT_TO_PBV(κ(x), χ(x))` substitutions so the model
  // layer can reconstruct PBV values from the int model. Without these,
  // get-value on a PBV term dereferences a null NodeValue and crashes.
  void addSkolemDefinitions(const std::map<Node, Node>& skolems);

  PIntBlaster d_intBlaster;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* __CVC5__PREPROCESSING__PASSES__PBV_TO_INT_H */
