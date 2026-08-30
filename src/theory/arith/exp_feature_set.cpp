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
 * See exp_feature_set.h.
 */

#include "theory/arith/exp_feature_set.h"

#include <algorithm>
#include <cctype>

namespace cvc5::internal {
namespace theory {
namespace arith {

namespace {
/**
 * The SwInE lemma families covered by the 'all-lemmas' aggregate: the five
 * families this solver implements. 'compose' is deliberately excluded -- it is
 * reachable only by naming it explicitly or via 'all'.
 */
bool isSwineLemmaFamily(const std::string& n)
{
  return n == "symmetry" || n == "bounding" || n == "prime" || n == "induction"
         || n == "interpolation";
}
}  // namespace

ExpFeatureSet::ExpFeatureSet(const std::string& spec)
{
  std::string tok;
  auto flush = [&]() {
    if (tok.empty()) return;
    std::transform(tok.begin(), tok.end(), tok.begin(), [](unsigned char c) {
      return std::tolower(c);
    });
    if (tok == "all")
    {
      d_all = true;
    }
    else if (tok == "all-lemmas")
    {
      d_allLemmas = true;
    }
    else if (tok == "swine")
    {
      // The preprocessing of SwInE Sect. 4.1: constant folding plus the three
      // rewrite rules
      //   exp(x,c) -> x^|c| (c constant), exp(exp(x,y),z) -> exp(x,y*z),
      //   exp(x,y)*exp(z,y) -> exp(x*z,y).
      // Note that 'fuse' -- exp(x,y)*exp(x,z) -> exp(x,y+z) -- is NOT part of
      // this set: Sect. 4.1 names it as unsound, and it is unsound here too
      // (exp(x,1)*exp(x,-1) = x * (1 div x) = 0 for x >= 2, but exp(x,0) = 1).
      d_names.insert("const");
      d_names.insert("compose");
      d_names.insert("fuse-base");
      d_names.insert("unroll");
    }
    else if (tok == "symmetry-interpolation")
    {
      // Legacy compound name, still used by run_experiments_exp.sh. Kept as an
      // alias so existing evaluation scripts keep working; the list form
      // 'symmetry,interpolation' is equivalent.
      d_names.insert("symmetry");
      d_names.insert("interpolation");
    }
    else if (tok == "symmetry-refine")
    {
      // Legacy name from when 'symmetry' meant static initial-refine axioms
      // and 'symmetry-refine' meant the full-refinement variant. Every family
      // is now full-refinement and model-guarded, so this selects the same
      // behaviour as 'symmetry'.
      d_names.insert("symmetry");
    }
    else if (tok != "none")
    {
      // 'none' contributes nothing, so listing it alongside others is
      // harmless rather than an error.
      d_names.insert(tok);
    }
    tok.clear();
  };
  for (char c : spec)
  {
    if (c == ',' || c == ' ' || c == '+' || c == ';')
    {
      flush();
    }
    else
    {
      tok.push_back(c);
    }
  }
  flush();
}

bool ExpFeatureSet::has(const std::string& name) const
{
  // 'unroll' is deliberately NOT implied by 'all': expanding EXP(s,c) into c
  // copies of s can blow up term size, so it must always be named explicitly.
  // 'fuse' is not implied either, and for a stronger reason -- it is the
  // rewrite exp(x,y)*exp(x,z) -> exp(x,y+z) that Frohn & Giesl Sect. 4.1 names
  // as unsound, and it is unsound under this solver's semantics as well
  // (exp(s,1)*exp(s,-1) = s * (1 div s) = 0 for s >= 2, but exp(s,0) = 1).
  // Otherwise 'all' covers every family, including the term-introducing
  // variants.
  if (d_all && name != "unroll" && name != "fuse")
  {
    return true;
  }
  if (d_allLemmas && isSwineLemmaFamily(name))
  {
    return true;
  }
  return d_names.find(name) != d_names.end();
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
