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
 * Multi-width PBV rewrites, applied BEFORE the translation to NIA.
 * Enabled by --pbv-preprocess-mw.
 */

#ifndef CVC5__PREPROCESSING__PASSES__PBV_MW_H
#define CVC5__PREPROCESSING__PASSES__PBV_MW_H

#include <map>
#include <unordered_map>
#include <vector>

#include "preprocessing/passes/int_order_facts.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * Width-aware PBV rewrites that the RARE rewriter cannot express.
 *
 * The `pbv-mw-*` RARE rules never fire on real benchmarks for two reasons:
 *
 *   CAUSE 1 - normal form.  A RARE condition compares Nodes syntactically, so
 *   it builds `(- (pbvsize x) 1)` with Kind::SUB and tests node equality. But
 *   cvc5's arithmetic rewriter eliminates SUB, so the term in the assertion is
 *   never a SUB node and the guard can never hold.
 *
 *   CAUSE 2 - semantics.  Benchmarks write the extract bound as `(- r 1)` and
 *   tie r to a width elsewhere, via `(assert (= (pbvsize v) r))`. That link is
 *   an assertion, not syntax, and a rewriter cannot consult it.
 *
 * This pass fixes both.  It runs before pbv-to-int, so it sees the whole
 * assertion list:
 *   * CAUSE 2 is handled by harvesting every `(= (pbvsize x) V)` into an alias
 *     map, so widthOf() reports widths in terms of the user's own variables.
 *   * CAUSE 1 is handled by deciding each side condition as
 *     `rewrite(a - b)` == 0 rather than by node equality, which normalises both
 *     sides through the arithmetic rewriter first.
 *
 * Removing an extension here rather than after translation matters because
 * psign_extend's integer encoding is an msb ITE plus two extra pow2 terms and
 * a product; once the int-blaster has built that, it cannot be undone.
 */
class PbvMw : public PreprocessingPass
{
 public:
  PbvMw(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /** Collect `(= (pbvsize x) V)` links from every assertion (CAUSE 2). */
  void harvestWidths(const std::vector<Node>& assertions);
  /** Collect from one assertion, descending only through conjunctions. */
  void harvestFrom(TNode a);

  /**
   * Symbolic width of a PBV term, expressed in the user's width variables
   * wherever the alias map allows.
   */
  Node widthOf(TNode t);

  /** Is `a == b` as integers?  Decided via rewrite(a - b) == 0 (CAUSE 1). */
  bool widthEq(Node a, Node b);

  /** Order facts harvested from the assertions, for the `m >= 1` side
   * condition of the sext-over-zext rule (--pbv-sext-to-zext). */
  IntOrderFacts d_facts;

  /** Bottom-up rewrite of n. */
  Node rewriteRec(TNode n);
  /** Apply the multi-width rules at the top of an already-rewritten node. */
  Node applyRules(Node n);

  /** True for PBV_ZERO_EXTEND / PBV_SIGN_EXTEND. */
  static bool isExtend(TNode n);

  /** Peel every pzero_extend off the front of a term. */
  static TNode stripZext(TNode n);
  /** True for the operators a low extract may be pushed through. */
  static bool isPushOp(Kind k);

  void bump(const char* rule);

  /** `(pbvsize x)` -> the Int variable it was equated with. */
  std::unordered_map<Node, Node> d_sizeAlias;
  std::unordered_map<Node, Node> d_widthCache;
  std::unordered_map<Node, Node> d_cache;
  /** Per-rule firing counts, for -t pbv-mw. */
  std::map<std::string, uint64_t> d_fired;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__PBV_MW_H */
