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


ExpFeatureSet::ExpFeatureSet(const std::string& spec, ExpFeatureAxis axis)
    : d_axis(axis)
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
      if (axis != ExpFeatureAxis::LEMMAS)
      {
        tok.clear();
        return;
      }
      // On the LEMMA axis 'all' starts from the tuned exponential selection
      // 'exp-fuse-model', so it also carries the explicit-only selections that
      // one names (negone-parity, halving, neg-recip, fuse-model). Without
      // them 'all' lost 14 satisfiable LoAT instances against exp-fuse-model.
      tok = "exp-fuse-model";
    }
    if (tok == "swine" && axis == ExpFeatureAxis::REWRITES)
    {
      // The preprocessing of SwInE Sect. 4.1: constant folding plus the three
      // rewrite rules
      //   exp(x,c) -> x^|c| (c constant), exp(exp(x,y),z) -> exp(x,y*z),
      //   exp(x,y)*exp(z,y) -> exp(x*z,y).
      // Note that 'fuse' -- exp(x,y)*exp(x,z) -> exp(x,y+z) -- is NOT part of
      // this set: Sect. 4.1 names it as unsound, and it is unsound here too
      // (exp(x,1)*exp(x,-1) = x * (1 div x) = 0 for x >= 2, but exp(x,0) = 1).
      // 'compose' is NOT inserted: the exponent-composition rewrite was
      // removed as unsound under this solver's `**` semantics (see the note
      // in ArithRewriter). Its guarded form is --arith-exp-lemmas=compose.
      d_names.insert("const");
      d_names.insert("fuse-base");
      d_names.insert("unroll");
    }
    else if ((tok == "exp" || tok == "exp-full" || tok == "exp-no-phasing"
              || tok == "exp-fuse-model")
             && axis == ExpFeatureAxis::LEMMAS)
    {
      // The tuned selection for the exponential / QF_EIA (LoAT) workload, the
      // counterpart of 'pbv'. Equivalent to spelling out:
      //   symmetry,prime,induction,interpolation,compose,fuse,fuse-base,mon,
      //   negone-parity,halving,phasing,const,unroll
      //
      // 'exp-full' is an ALIAS for 'exp' and selects exactly the same list.
      // The two used to differ outside it -- 'exp' additionally switched on a
      // singleton-elimination / congruence-decision pair that 'exp-full' left
      // alone. That pair has since been removed from the solver, so nothing
      // now distinguishes the two spellings; 'exp-full' is kept only so
      // scripts naming it keep working.
      // Note it names 'negone-parity' and 'halving' explicitly -- neither is
      // implied by 'all', and on this workload they are the two that matter
      // most: (-1)^t is the only exponential in most of these files, and the
      // predecessor chain is what ties 2^t to 2^(t-1).
      //
      // 'const' and 'unroll' are not lemma families at all: they are the two
      // REWRITE schemas of --arith-exp-rewrites, which the ArithRewriter also
      // reads off this axis (the two axes are OR-ed for these two tokens
      // only). They are here because this workload is full of polynomial
      // powers with small constant exponents, and unrolling them is what lets
      // ordinary nonlinear arithmetic see them at all. Unlike on the rewrite
      // axis, where 'unroll' is explicit-only, the lemma-axis 'all' implies
      // both -- 'all' means all here.
      d_names.insert("symmetry");
      d_names.insert("prime");
      d_names.insert("induction");
      d_names.insert("interpolation");
      d_names.insert("compose");
      d_names.insert("fuse");
      d_names.insert("fuse-base");
      d_names.insert("mon");
      d_names.insert("negone-parity");
      d_names.insert("halving");
      // 'exp-no-phasing' is 'exp-full' with the phasing search strategy left
      // out: phasing loses satisfiable instances (it is a search strategy,
      // not a lemma family), so a run line that wants every lemma family of
      // 'exp-full' but a plain search names this instead. Only the 'phasing'
      // token is withheld; note --arith-exp-phasing given explicitly is
      // OR-ed in by the ExpSolver and still wins.
      if (tok != "exp-no-phasing")
      {
        d_names.insert("phasing");
      }
      // the two rewrite schemas readable from this axis, see above
      d_names.insert("const");
      d_names.insert("unroll");
      // 'exp-full' is 'exp' plus the negative-reciprocal lemma in the
      // full-refinement loop, t < 0 => exp(s,t) = 1 div exp(s,-t) -- the
      // same selection as --arith-exp-neg-recip=refine, and the two are
      // OR-ed. This is the one thing that now separates the two spellings.
      // 'exp-no-phasing' carries it too: it is 'exp-full' minus phasing.
      if (tok == "exp-full" || tok == "exp-no-phasing"
          || tok == "exp-fuse-model")
      {
        d_names.insert("neg-recip");
      }
      // 'exp-fuse-model' is 'exp-full' plus the model-matched fusion.
      if (tok == "exp-fuse-model")
      {
        d_names.insert("fuse-model");
      }
      // Keep the aggregate name itself, so SetDefaults can see WHICH of the
      // two was asked for. Note it must not key off 'halving': both
      // selections name it, and so would a bare --arith-exp-lemmas=halving,
      // which deliberately no longer pulls the two options in.
      d_names.insert(tok);
    }
    else if (tok == "pbv")
    {
      // The tuned selection for the PBV-to-int workload. It means different
      // things on the two axes, so it expands per axis -- the lemma side
      // includes the guarded 'fuse' lemma, which has no rewrite-side
      // counterpart.
      if (axis == ExpFeatureAxis::REWRITES)
      {
        // Equivalent to spelling out: unroll,const. 'compose' used to be here
        // too, until the composition rewrite was removed as unsound. Its
        // guarded replacement is the 'compose' LEMMA, which the lemma-axis
        // 'pbv' set below now includes, so the capability stays in the run
        // line -- it just moved axes.
        d_names.insert("unroll");
        d_names.insert("const");
      }
      else
      {
        // Everything the ExpSolver has that pays off there, including the
        // selections no other aggregate implies ('fuse', 'mon') or that lives
        // outside the family list altogether ('phasing'). Equivalent to
        //   interpolation,symmetry,prime,induction,fuse,bounding,mon,
        //   phasing,compose
        // 'compose' is here because the rewrite-axis 'pbv' set used to carry
        // the composition rewrite; that rewrite was removed as unsound, and
        // this guarded lemma is where the capability went.
        d_names.insert("compose");
        d_names.insert("interpolation");
        d_names.insert("symmetry");
        d_names.insert("prime");
        d_names.insert("induction");
        d_names.insert("fuse");
        d_names.insert("bounding");
        d_names.insert("mon");
        d_names.insert("phasing");
      }
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
  // An explicit mention always wins, including alongside 'all'. The exclusions
  // below say only that 'all' does not IMPLY these selections -- not that it
  // suppresses one the user went on to name, which is what 'all,halving' and
  // 'all,unroll' would otherwise mean.
  if (d_names.find(name) != d_names.end())
  {
    return true;
  }
  if (d_all)
  {
    // On the LEMMA axis 'all' is 'exp-fuse-model' (expanded into d_names by
    // the parser) plus every other family except 'bounding', including
    // 'fuse', 'mon', 'fuse-base' and 'phasing'. Note two of those
    // are not simply additive -- 'mon' SUPPRESSES the two same-base pair
    // monotonicity lemmas, and 'phasing' is a search strategy rather than a
    // lemma family -- so 'all' is a genuinely different configuration from
    // naming the five SwInE families, not merely a larger one.
    if (d_axis == ExpFeatureAxis::LEMMAS)
    {
      // Two exceptions, both explicit-only.
      //
      // 'negone-parity' is not merely a lemma: it drives a PREPROCESSING pass,
      // which is where all of its value is (the ExpSolver lemma is a fallback
      // for a base only discovered to be -1 later).
      //
      // 'halving' INTRODUCES new EXP terms, exp(s,t-1) and onwards. That is
      // the same property that keeps 'unroll' out of 'all' on the rewrite
      // axis, and for the same reason: a selection that grows the term set has
      // to be asked for.
      //
      // Folding either into 'all' would silently change what every recorded
      // 'all' run means.
      // 'exp', 'exp-full', 'exp-no-phasing' and 'pbv' are aggregate NAMES,
      // not features, so
      // 'all' must not answer yes to "was this aggregate asked for?".
      //
      // The rewrite schemas 'const' and 'unroll', which the ArithRewriter also
      // reads off this axis, are NOT excepted: 'all' means all here, so it
      // turns both on -- note this differs from the rewrite axis below, where
      // 'unroll' stays explicit-only.
      //
      // 'neg-recip' is likewise explicit-only: it is the 'refine' placement
      // of --arith-exp-neg-recip, which has its own option and its own
      // default of 'off', and folding it into 'all' would change every
      // recorded 'all' baseline. It is selected by 'exp-full'.
      return name != "negone-parity" && name != "halving" && name != "exp"
             && name != "exp-full" && name != "exp-no-phasing"
             && name != "exp-fuse-model"
             && name != "pbv" && name != "neg-recip"
             && name != "fuse-model"
             // 'bounding' is explicit-only too: it costs QF_EIA instances
             // (PURRS/purrs31 goes from 0.3s to a timeout). Name it, or give
             // --arith-exp-bounding, to have it alongside 'all'.
             && name != "bounding";
    }
    // On the REWRITE axis 'unroll' stays excluded: expanding EXP(s,c) into c
    // copies of s can blow up term size, so it must always be named
    // explicitly. Every other schema is covered.
    return name != "unroll";
  }
  return false;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
