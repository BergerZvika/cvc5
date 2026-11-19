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
 * The conditional rewrite families selected by --learned-rewrite-rules.
 *
 * Every family here is a rewrite whose side condition is decided against
 * facts (the order facts of the assertions, plus the learned literals of
 * non-clausal simplification where those exist) or against a structural
 * match the unconditional families do not need. They run in the
 * learned-rewrite passes:
 *
 *   learned-rewrite-pbv  before pbv-to-int, on the PBV assertions (the
 *                        conditional rules of the pbv-mw engine)
 *   learned-rewrite      after pbv-to-int, on the integer assertions (the
 *                        mod-2^k reducer)
 *
 * Aggregates: ext-norm, pbv (every PBV family), pbv-min (exactly the rules
 * of the paper's learned-rewrite table), int (reduce-mods, reduce-mods-width),
 * exp (every integer family, no PBV family), all.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__LEARNED_REWRITE_RULES_H
#define CVC5__PREPROCESSING__PASSES__LEARNED_REWRITE_RULES_H

#include <string>

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

struct LearnedRewriteRules
{
  // -- PBV level (learned-rewrite-pbv) ------------------------------------
  /** A1/A2, B1/B2: low extract at / through an extension, w(x) = i+1. */
  bool d_preprocessMw = false;
  /** E, E2: sign extension over a zero extension by >= 1 bit. */
  bool d_sextToZext = false;
  /** F: ((x << c) + y) >> c -> x + (y >> c), s >= p + 2^u - 1. */
  bool d_shiftAddDistrib = false;
  /** M2: symbolic low mask, 1 <= m <= w. */
  bool d_maskSlice = false;
  /** M3: extract through shl under z <u m (mask-slice, not pbv-min). */
  bool d_maskSliceShl = false;
  /** T1, T5: the width-conditioned truncation pushes. */
  bool d_truncPush = false;
  /** T0, T4: the full and the nested extract (trunc-push, not pbv-min). */
  bool d_truncPushNest = false;
  /** X1 at equal widths, X3: extensions out of bitwise operators /
   * equalities. */
  bool d_extBitwise = false;
  /** X1 at unequal widths, widening the narrower operand (ext-bitwise, not
   * pbv-min). */
  bool d_extBitwiseWiden = false;
  /** S1, S3: one-bit sign extension, w(c) = 1. */
  bool d_sextBv1 = false;
  /** I3: (a << K) >>s K, 0 <= m <= w-1. */
  bool d_sextIdioms = false;
  /** R1, R2: -2^m against a sign extension. */
  bool d_signedRange = false;
  /** W2: a shift and its inverse leave a mask (shift-bitwise, shift-pair). */
  bool d_shiftBitwise = false;
  /** W3: a ones-shift absorbed by a shift by the same amount (shift-bitwise,
   * shift-mask-absorb). */
  bool d_shiftMaskAbsorb = false;
  /** W4: equal extensions out of a bitwise operator (shift-bitwise,
   * ext-out-bitwise). */
  bool d_extOutBitwise = false;
  /** G2a, G4, G5c: sign idioms with a constant / shape condition. */
  bool d_signIdioms = false;
  /** K1, K2, K3: rules over harvested mask facts. */
  bool d_maskFacts = false;
  /** K3 alone (pbv-min, which leaves out K1 and K2). */
  bool d_maskFactsIte = false;
  /** K4: (~a | b) = ones -> (a & b) = a, w(ones) = w(a). */
  bool d_subsetFacts = false;
  // -- integer level (learned-rewrite) ------------------------------------
  /** Cases 1-5 of the mod-2^k reducer (strip subsumed inner mods). */
  bool d_reduceMods = false;
  /** Group A, cases 11, 13 of the mod-2^k reducer (width bounds). */
  bool d_reduceModsWidth = false;
  /** Case 20 of the mod-2^k reducer (drop 2^e = 0 shift guards). */
  bool d_shiftGuardElim = false;

  bool anyPbv() const;
  bool anyInt() const;
  /** The bitwise families that need the width classes of pbv-mw. */
  bool anyBitwise() const;

  /**
   * Parse a comma-separated token list. Returns false and sets `bad` to the
   * offending token on an unknown token.
   */
  bool parse(const std::string& list, std::string& bad);
  /** Parse a list already validated by setDefaults. */
  static LearnedRewriteRules fromString(const std::string& list);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__LEARNED_REWRITE_RULES_H */
