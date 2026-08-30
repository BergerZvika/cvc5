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
 * Post-translation reduction of `mod` by a power, for an arbitrary base.
 * Enabled by --exp-reduce-mod-pow.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__EXP_MOD_POW_H
#define CVC5__PREPROCESSING__PASSES__EXP_MOD_POW_H

#include <unordered_map>
#include <unordered_set>

#include "expr/node.h"
#include "preprocessing/passes/int_order_facts.h"
#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * Rewrites a modulus whose divisor is a power into a case split on the two
 * exponents, for any base s that is known to be at least 2:
 *
 *   (mod (exp s a) (exp s b))
 *       -->  ite(a >= b, 0, (exp s a))
 *
 *   (mod (* x (exp s a)) (exp s b))
 *       -->  ite(a >= b, 0, (* (mod x (exp s (- b a))) (exp s a)))
 *
 * Both are valid for s >= 2 and a, b >= 0. The first is divisibility of
 * powers, s^b | s^a whenever a >= b; the second is the standard identity
 * (x*m) mod (m*n) = m * (x mod n) instantiated at m = s^a, n = s^(b-a).
 *
 * The point is what the rewrite REMOVES. cvc5 expands `y mod d` into
 * y = d*q + r with a fresh q, so a symbolic divisor d = s^b contributes a
 * product of two non-constant terms, which the nonlinear extension can only
 * approach through tangent planes -- on the PBV/syrew translations that is
 * where essentially all of the time goes. Neither replacement contains such a
 * product: the first is a constant or an existing term, and in the second the
 * surviving `mod` has been narrowed to the divisor s^(b-a).
 *
 * The facts s >= 2, a >= 0 and b >= 0 are side conditions, so the rewrite is
 * applied only where they can be discharged -- from constants, from the
 * structure of the term itself (a `mod` by a positive power is non-negative, a
 * power of a base >= 2 is non-negative), or from the order facts harvested
 * from the assertions. Where they cannot be discharged the term is left alone.
 * Nothing is applied below a quantifier, since the harvested facts constrain
 * free symbols only.
 */
class ExpModPow : public PreprocessingPass
{
 public:
  ExpModPow(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /** What the assertions entail about the two exponents of a rewrite. */
  enum class Order
  {
    GEQ,      // a >= b is entailed
    LT,       // a <  b is entailed
    UNKNOWN,  // neither, so the rewrite must keep the case split
  };
  /**
   * Decide the order of the two exponents, so that a rewrite can take the
   * relevant branch directly instead of leaving an `ite(a >= b, ..)` for the
   * SAT solver. Problems whose widths are ordered by their own assertions --
   * a widening extend asserts p < q -- get this for free from IntOrderFacts.
   */
  Order compareExps(TNode a, TNode b);
  /** Memoized bottom-up rewrite of n. */
  Node convert(TNode n);
  /**
   * Apply the two rules at n, which has already had its children converted.
   * Returns the null node when neither applies.
   */
  Node tryRules(TNode n);
  /** Is `2 <= s` entailed? */
  bool baseAtLeastTwo(TNode s);
  /** Is `0 <= e` entailed? Structural cases first, then the order facts. */
  bool nonNeg(TNode e);
  /** Is `d` a `mod` divisor we know to be non-zero, i.e. a power of a base >= 2? */
  bool isPositivePower(TNode d);

  /** Order facts harvested from the assertions, for the side conditions. */
  IntOrderFacts d_facts;
  /** Rewrite cache. */
  std::unordered_map<Node, Node> d_cache;
  /** Memo for nonNeg. */
  std::unordered_map<Node, bool> d_nonNeg;
  /** Number of applications of each rule, for the trace. */
  uint64_t d_numPow = 0;
  uint64_t d_numMult = 0;
  /** How many of those had their exponent order entailed rather than split. */
  uint64_t d_numDecided = 0;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__EXP_MOD_POW_H */
