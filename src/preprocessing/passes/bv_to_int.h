/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The bv-to-int preprocessing pass.
 */

#ifndef __CVC5__PREPROCESSING__PASSES__BV_TO_INT_H
#define __CVC5__PREPROCESSING__PASSES__BV_TO_INT_H

#include "context/cdhashmap.h"
#include "context/cdo.h"
#include "context/context.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/bv/int_blaster.h"
#include "theory/pbv/int_blaster.h"

#include <unordered_map>

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using CDNodeMap = context::CDHashMap<Node, Node>;

class BVToInt : public PreprocessingPass
{
 public:
  BVToInt(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

  // Add the lemmas in `additionalConstraints` to the assertions pipeline.
  void addFinalizeAssertions(
      AssertionPipeline* assertionsToPreprocess,
      const std::vector<TrustNode>& additionalConstraints);

  // include the skolem map as substitutions
  void addSkolemDefinitions(const std::map<Node, Node>& skolems);

  // Lift a BV node to a PBV node. Returns a null Node if any subterm uses
  // a BV kind we don't yet handle in PBV mode (caller leaves assertion as-is).
  // BV variables become `(int_to_pbv k chi_x)` with a fresh integer skolem
  // `chi_x`; range/skolem-definition bookkeeping is captured in members so the
  // caller can install range lemmas and model-recovery substitutions.
  Node liftBvToPbv(Node n);

  IntBlaster d_intBlaster;
  // Only constructed lazily when mode==PBV.
  std::unique_ptr<PIntBlaster> d_pIntBlaster;
  // BV-var → fresh PBV-var the lifter substituted in.
  std::unordered_map<Node, Node> d_bvVarPbv;
  // Memoization for liftBvToPbv.
  std::unordered_map<Node, Node> d_liftCache;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* __CVC5__PREPROCESSING__PASSES__BV_TO_INT_H */
