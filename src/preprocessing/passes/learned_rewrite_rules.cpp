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
  return d_shiftBitwise || d_signIdioms || d_maskFacts;
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
    // exp: every integer-level family and nothing at the PBV level, for
    // integer / exponential input (the mod-2^k reducer acts on `mod x (** 2 k)`
    // whether or not it came from a PBV translation).
    bool exp = all || tok == "exp";
    bool intg = exp || tok == "int";
    if (tok.empty() || tok == "none") continue;
    bool known = all || pbv || extNorm || intg || exp;
    auto pick = [&](bool agg, const char* name, bool& field) {
      if (agg || tok == name)
      {
        field = true;
        known = true;
      }
    };
    pick(pbv, "preprocess-mw", d_preprocessMw);
    pick(pbv, "sext-to-zext", d_sextToZext);
    pick(pbv, "shift-add-distrib", d_shiftAddDistrib);
    pick(pbv, "mask-slice", d_maskSlice);
    pick(extNorm, "trunc-push", d_truncPush);
    pick(extNorm, "ext-bitwise", d_extBitwise);
    pick(extNorm, "sext-bv1", d_sextBv1);
    pick(extNorm, "sext-idioms", d_sextIdioms);
    pick(extNorm, "signed-range", d_signedRange);
    pick(pbv, "shift-bitwise", d_shiftBitwise);
    pick(pbv, "sign-idioms", d_signIdioms);
    pick(pbv, "mask-facts", d_maskFacts);
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
