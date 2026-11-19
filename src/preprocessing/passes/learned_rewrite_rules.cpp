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
 * See learned_rewrite_rules.h.
 */

#include "preprocessing/passes/learned_rewrite_rules.h"

#include <sstream>

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

bool LearnedRewriteRules::anyPbv() const
{
  return d_preprocessMw || d_sextToZext || d_shiftAddDistrib || d_maskSlice
         || d_truncPush || d_extBitwise || d_sextBv1 || d_sextIdioms
         || d_signedRange || anyBitwise();
}

bool LearnedRewriteRules::anyInt() const
{
  return d_reduceMods || d_reduceModsWidth || d_shiftGuardElim;
}

bool LearnedRewriteRules::anyBitwise() const
{
  return d_shiftBitwise || d_shiftMaskAbsorb || d_extOutBitwise || d_signIdioms || d_maskFacts || d_maskFactsIte
         || d_subsetFacts;
}

bool LearnedRewriteRules::parse(const std::string& list, std::string& bad)
{
  std::stringstream ss(list);
  std::string tok;
  while (std::getline(ss, tok, ','))
  {
    // tolerate surrounding blanks
    size_t b = tok.find_first_not_of(" \t");
    size_t e = tok.find_last_not_of(" \t");
    tok = b == std::string::npos ? "" : tok.substr(b, e - b + 1);
    bool all = tok == "all";
    bool pbv = all || tok == "pbv";
    bool extNorm = pbv || tok == "ext-norm";
    // pbv-min: the rules of the paper's learned-rewrite table (Table 7) and
    // nothing else -- every PBV family but shift-bitwise and sign-idioms, and
    // trunc-push / ext-bitwise without T0, T4 and the widening X1, and
    // mask-facts without K1 (ult-mask, ule-mask) and K2 (and-mask-sub), and
    // mask-slice without M3 (extract-shl).
    bool pbvMin = tok == "pbv-min";
    // pbv-tuned: the PBV tokens that each measured positive in the per-family
    // ablation (sign-idioms, mask-facts); shift-bitwise lost on syrew.
    // pbv-tuned-plus: pbv-tuned plus W3 and W4 of shift-bitwise, which gained
    // on alive and syrew and lost nothing; W2 (shift-pair) is left out, it
    // caused every loss of shift-bitwise on syrew and rewrite.
    bool pbvTunedPlus = tok == "pbv-tuned-plus";
    bool pbvTuned = pbvTunedPlus || tok == "pbv-tuned";
    // exp: every integer-level family and nothing at the PBV level, for
    // integer / exponential input (the mod-2^k reducer acts on `mod x (** 2 k)`
    // whether or not it came from a PBV translation).
    bool exp = all || tok == "exp";
    bool intg = exp || tok == "int";
    if (tok.empty() || tok == "none") continue;
    bool known = all || pbv || extNorm || pbvMin || pbvTuned || intg || exp;
    auto pick = [&](bool agg, const char* name, bool& field) {
      if (agg || tok == name)
      {
        field = true;
        known = true;
      }
    };
    pick(pbv || pbvMin, "preprocess-mw", d_preprocessMw);
    pick(pbv || pbvMin, "sext-to-zext", d_sextToZext);
    pick(pbv || pbvMin, "shift-add-distrib", d_shiftAddDistrib);
    pick(pbv || pbvMin, "mask-slice", d_maskSlice);
    pick(pbv, "mask-slice", d_maskSliceShl);
    pick(extNorm || pbvMin, "trunc-push", d_truncPush);
    pick(extNorm, "trunc-push", d_truncPushNest);
    pick(extNorm || pbvMin, "ext-bitwise", d_extBitwise);
    pick(extNorm, "ext-bitwise", d_extBitwiseWiden);
    pick(extNorm || pbvMin, "sext-bv1", d_sextBv1);
    pick(extNorm || pbvMin, "sext-idioms", d_sextIdioms);
    pick(extNorm || pbvMin, "signed-range", d_signedRange);
    pick(pbv, "shift-bitwise", d_shiftBitwise);
    pick(pbv, "shift-bitwise", d_shiftMaskAbsorb);
    pick(pbv, "shift-bitwise", d_extOutBitwise);
    // the three rules of shift-bitwise one at a time: W2, W3, W4
    pick(false, "shift-pair", d_shiftBitwise);
    pick(pbvTunedPlus, "shift-mask-absorb", d_shiftMaskAbsorb);
    pick(pbvTunedPlus, "ext-out-bitwise", d_extOutBitwise);
    pick(pbv || pbvTuned, "sign-idioms", d_signIdioms);
    pick(pbv || pbvTuned, "mask-facts", d_maskFacts);
    pick(pbv || pbvMin || pbvTuned, "mask-facts", d_maskFactsIte);
    pick(pbv, "subset-facts", d_subsetFacts);
    pick(intg, "reduce-mods", d_reduceMods);
    pick(intg, "reduce-mods-width", d_reduceModsWidth);
    pick(exp, "shift-guard-elim", d_shiftGuardElim);
    if (!known)
    {
      bad = tok;
      return false;
    }
  }
  return true;
}

LearnedRewriteRules LearnedRewriteRules::fromString(const std::string& list)
{
  LearnedRewriteRules r;
  std::string bad;
  r.parse(list, bad);
  return r;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
