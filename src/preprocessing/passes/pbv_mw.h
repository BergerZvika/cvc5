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
 *
 * The rule engine is shared by two passes. pbv-mw runs the UNCONDITIONAL
 * families, each behind its own --pbv-* flag. learned-rewrite-pbv (see
 * learned_rewrite_pbv.h) runs the same engine with the CONDITIONAL rules
 * switched on as well, selected by --learned-rewrite-rules, and replaces
 * pbv-mw when it runs; the conditional bodies are in learned_rewrite_pbv.cpp
 * and are reached through the lr* hooks below, called from the same
 * positions they always held, so the two kinds still reach a common fixed
 * point.
 */

#ifndef CVC5__PREPROCESSING__PASSES__PBV_MW_H
#define CVC5__PREPROCESSING__PASSES__PBV_MW_H

#include <map>
#include <set>
#include <unordered_set>
#include <unordered_map>
#include <vector>

#include "preprocessing/passes/int_order_facts.h"
#include "preprocessing/passes/learned_rewrite_rules.h"
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
  /**
   * The engine under another pass name, with the conditional families of
   * `cond` enabled (learned-rewrite-pbv).
   */
  PbvMw(PreprocessingPassContext* preprocContext,
        const std::string& name,
        const LearnedRewriteRules& cond);

  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

  /** The conditional families to run; all off for pbv-mw itself. */
  LearnedRewriteRules d_cond;

  // ---- conditional rules (--learned-rewrite-rules), learned_rewrite_pbv.cpp.
  // Each returns n unchanged when no rule fires or its family is off.
  /** T0: t[i:0] -> t when w(t) = k. */
  Node lrTruncPushFull(Node n, TNode t, Node kw);
  /** T1, T4, T5 on an admissible t = n[0]; kw = i + 1. */
  Node lrTruncPushCut(Node n, TNode t, Node i, Node kw);
  /** X1, X3. */
  Node lrExtBitwise(Node n);
  /** S1, S3. */
  Node lrSextBv1(Node n);
  /** I3. */
  Node lrSextIdioms(Node n);
  /** R1, R2. */
  Node lrSignedRange(Node n);
  /** W2, W4, W3. */
  Node lrShiftBitwise(Node n);
  /** G2a, G4. */
  Node lrSignIdioms(Node n);
  /** G5c for the summand n[i]. */
  Node lrSignIdiomsAddIte(Node n, size_t i);
  /** K1, K2, K3. */
  Node lrMaskFacts(Node n);
  /** K4. */
  Node lrSubsetFacts(Node n);
  /** F, E, E2, M2, M3, A/B. */
  Node lrRules(Node n);

 private:
  /** Collect `(= (pbvsize x) V)` links from every assertion (CAUSE 2). */
  void harvestWidths(const std::vector<Node>& assertions);
  /** Collect from one assertion, descending only through conjunctions. */
  void harvestFrom(TNode a);

  /** Collect `(pbvult t (int_to_pbv w m))` bounds, for rule M3's `z <u m`
   * side condition (--pbv-mask-slice). */
  void harvestUltBounds(const std::vector<Node>& assertions);
  /** Collect from one assertion, descending only through conjunctions. */
  void harvestUltFrom(TNode a);

  /**
   * Symbolic width of a PBV term, expressed in the user's width variables
   * wherever the alias map allows.
   */
  Node widthOf(TNode t);

  /** Is `a == b` as integers?  Decided via rewrite(a - b) == 0 (CAUSE 1). */
  bool widthEq(Node a, Node b);

  /**
   * Is `m >= 1` known?  Either the order facts entail it, or `m` IS a width:
   * every T_PBV term has a positive width, but the pbv-mw pass runs BEFORE
   * pbv-to-int states Adm(phi), so the fact is not yet among the assertions.
   */
  bool widthPositive(TNode m);

  /** Order facts harvested from the assertions, for the `m >= 1` side
   * condition of every conditional rule (--learned-rewrite-rules). */
  IntOrderFacts d_facts;

  /** Bottom-up rewrite of n. */
  Node rewriteRec(TNode n);
  /** Apply the multi-width rules at the top of an already-rewritten node. */
  Node applyRules(Node n);
  /**
   * The extension-normalization families (--pbv-mw-trunc-push, -low-mask,
   * -ext-bitwise, -sext-bv1, -sext-idioms, -signed-range). Returns n when
   * none fires.
   */
  Node applyExtNorm(Node n);
  /**
   * The rules of the RW_B table (--pbv-rewrites-min) that live in this pass.
   * Returns n when none fires.
   */
  Node applyMin(Node n);
  /** Is `s` the value k-1 at its own width k (`int_to_pbv(k, k-1)` or
   * `int_to_pbv(k, k) - int_to_pbv(k, 1)`)? Sets `k` when it is. */
  bool isWidthMinusOne(TNode s, Node& k);
  /** The low extract t[i:0], itself normalized (--pbv-mw-trunc-push). */
  Node mkLowExtract(TNode t, Node i);
  /** Is `a <= b` known: equal after rewriting, or entailed by the facts? */
  bool widthLeq(Node a, Node b);
  /**
   * Are the local width side conditions of the top of t entailed: equal
   * operand widths, 0 <= j <= i < w for an extract, a non-negative extension,
   * a positive int_to_pbv width? A rule that deletes or restructures a node
   * may only fire when this holds, since PBV admits ill-typed terms and a
   * formula with no well-typed width assignment is unsatisfiable: dropping
   * an ill-typed node would drop that constraint with it.
   */
  bool admissible(TNode t);
  /**
   * Append to `out` the admissibility constraint Adm of every sub-term of
   * `assertions` (outside quantifiers), in the same shape the PBV int-blaster
   * emits it: positive leaf and int_to_pbv widths, extract bounds,
   * non-negative extensions, equal operand widths. The extension-normalization
   * rules may delete sub-terms; asserting the original Adm first means no
   * width constraint is lost with them, and the order facts can use it.
   */
  void pinAdmissibility(const std::vector<Node>& assertions,
                        std::vector<Node>& out);

  /** `(pbvnot (int_to_pbv w 0))`, `(int_to_pbv w -1)` or
   * `(pbvneg (int_to_pbv w 1))`. */
  static bool isOnes(TNode t);
  /** `(int_to_pbv w 0)`. */
  static bool isZero(TNode t);

  /** True for PBV_ZERO_EXTEND / PBV_SIGN_EXTEND. */
  static bool isExtend(TNode n);

  /** Peel every pzero_extend off the front of a term. */
  static TNode stripZext(TNode n);
  /** True for the operators a low extract may be pushed through. */
  static bool isPushOp(Kind k);

  /**
   * Is `t` the symbolic low mask `(1 << m) - 1` at some width?  Sets `m` to
   * the run length when it is.  Shared by M1's guard and M2 (--pbv-mask-slice).
   */
  static bool isLowMask(TNode t, Node& m);

  void bump(const char* rule);

  // ---- bitwise families (--pbv-mw-shift-bitwise, --pbv-mw-sign-idioms,
  //      learned mask-facts) -------------------------------------------------------
  /** The three bitwise families at the top of n; returns n when none fires. */
  Node applyBitwise(Node n);
  /** Flatten, sort, dedupe and fold the constants of an and/or/xor chain. */
  Node acNormBitwise(Node n);
  /** The width-class representative variable of a PBV term, or null. */
  Node widthLeaf(TNode t);
  /** `(pbvsize rep)` for t's width class, or `(pbvsize t)`. */
  Node widthTerm(TNode t);
  /**
   * Union the width classes of the variables the equal-width operators of
   * `assertions` relate, and fill d_widthSubst with
   * `(pbvsize v) -> (pbvsize rep)`. Sound once Adm is pinned: in every model
   * of it the two sizes are equal.
   */
  void buildWidthClasses(const std::vector<Node>& assertions);
  /** Harvest low-mask, disjointness and complement facts (mask-facts). */
  void harvestMaskFacts(const std::vector<Node>& assertions);
  /** If s is `int_to_pbv(K,K) - int_to_pbv(K,1)` (the value K-1 at width K),
   * return K. */
  static Node widthMinusOne(TNode s);
  /** Is t the msb mask `1 << (K-1)`? */
  static bool isMsbMask(TNode t);
  /** Is the and/or/xor term t, restricted to mask m, free of every operand
   * disjoint from m?  Returns t with those operands dropped. */
  Node dropDisjoint(TNode m, TNode t);
  bool areDisjoint(TNode a, TNode b) const;
  bool areComplements(TNode a, TNode b) const;

  std::unordered_map<Node, Node> d_widthParent;
  std::unordered_map<Node, Node> d_widthSubst;
  std::unordered_set<Node> d_lowMaskFacts;
  std::set<std::pair<Node, Node>> d_disjointFacts;
  std::set<std::pair<Node, Node>> d_complementFacts;

  /** `(pbvsize x)` -> the Int variable it was equated with. */
  std::unordered_map<Node, Node> d_sizeAlias;
  /** t -> m, from an asserted `(pbvult t (int_to_pbv w m))` (rule M3). */
  std::unordered_map<Node, Node> d_ultBound;
  std::unordered_map<Node, Node> d_widthCache;
  std::unordered_map<Node, Node> d_cache;
  /** Per-rule firing counts, for -t pbv-mw. */
  std::map<std::string, uint64_t> d_fired;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__PBV_MW_H */
