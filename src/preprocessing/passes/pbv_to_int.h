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
#include "preprocessing/passes/pbv_mod_reducer.h"
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

  // --pbv-to-int-reduce-mods: post-pass over the translated NIA assertions
  // that deletes `mod 2^k` operations made redundant by the width ordering.
  // Runs after every assertion has been blasted and after the RANGE/ADM
  // lemmas have been pushed, so the ordering facts it needs are all visible.
  void reduceRedundantPow2Mods(AssertionPipeline* assertionsToPreprocess);

  /**
   * --pbv-type-check. Build the width-only query that decides whether the
   * formula is well-sorted at all, and either discharge it now ('before'
   * modes) or hand it to the solver for use after an unsat verdict ('after'
   * modes).
   *
   * The query is Adm(phi) for the shallow checker. The deep checker conjoins
   * to it every top-level assertion whose free symbols are all widths, i.e.
   * the width constraints the formula itself imposes rather than only those
   * dictated by the syntax of its sub-terms. Dropping the other assertions
   * only weakens the query, so an unsatisfiable answer stays conclusive.
   */
  void typeCheck(AssertionPipeline* assertionsToPreprocess);
  /**
   * Is n a constraint about widths alone, i.e. does no PBV-sorted subterm
   * occur in it except directly under `pbvsize`? These are the constraints the
   * formula itself imposes on widths, which the deep checker adds to Adm(phi).
   */
  static bool isWidthOnly(TNode n);
  /**
   * Width constraints harvested from the input before translation. They are
   * collected there because the translation rewrites them away: with the
   * kappa union-find merging the widths that an operator forces to be equal,
   * `|x| = |y| + 1` becomes `k = k + 1` and simplifies to false, which is
   * indistinguishable from a bit-vector contradiction by the time the
   * assertion list is final.
   */
  std::vector<Node> d_widthAssertions;
  /** Conjunction of the constraints making up the selected checker's query. */
  Node buildTypeCheckQuery(AssertionPipeline* assertionsToPreprocess,
                           bool deep);

  PIntBlaster d_intBlaster;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* __CVC5__PREPROCESSING__PASSES__PBV_TO_INT_H */
