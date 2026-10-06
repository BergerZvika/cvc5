/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of exp solver.
 */

#include "theory/arith/nl/exp_solver.h"

#include "options/arith_options.h"
#include "options/smt_options.h"
#include "preprocessing/passes/bv_to_int.h"
#include <sstream>

#include "theory/arith/arith_msum.h"
#include "theory/arith/exp_feature_set.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

ExpSolver::ExpSolver(Env& env,
                     TheoryState& state,
                     InferenceManager& im,
                     NlModel& model)
    : EnvObj(env),
      d_astate(state),
      d_phaseB(1),
      d_phaseBound(2),
      d_phaseEmitted(userContext()),
      d_im(im),
      d_model(model),
      d_initRefine(userContext()),
      d_halveIntroduced(userContext())
{
  NodeManager* nm = nodeManager();
  d_false = nm->mkConst(false);
  d_true = nm->mkConst(true);
  d_zero = nm->mkConstInt(Rational(0));
  d_one = nm->mkConstInt(Rational(1));
  d_two = nm->mkConstInt(Rational(2));
  d_negone = nm->mkConstInt(Rational(-1));
}

ExpSolver::~ExpSolver() {}

void ExpSolver::initLastCall(const std::vector<Node>& xts)
{
  d_exps.clear();
  Trace("exp-mv") << "EXP terms : " << std::endl;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    if (ak != Kind::EXP)
    {
      // don't care about other terms
      continue;
    }
    d_exps.push_back(a);
  }
  Trace("exp") << "We have " << d_exps.size() << " exp terms." << std::endl;
}

void ExpSolver::checkInitialRefine()
{
  Trace("exp-check") << "ExpSolver::checkInitialRefine" << std::endl;
  // --arith-exp-value-only: no axioms, only value refinement (below).
  if (options().arith.expValueOnly)
  {
    return;
  }
  NodeManager* nm = nodeManager();
  for (const Node& i : d_exps)
  {
    if (d_initRefine.find(i) != d_initRefine.end())
    {
      // already sent initial axioms for i in this user context
      continue;
    }
    d_initRefine.insert(i);
    // initial refinement lemmas
    std::vector<Node> conj;
    ExpFeatureSet lselNegOne(options().arith.expLemmasMode,
                             ExpFeatureAxis::LEMMAS);
    Node s = i[0];
    Node t = i[1];

    // Phasing (Alg. 3 line 9): put this term's exponent under the level-b
    // bound, so the sat-phase is entered before the first full-refinement
    // round rather than after it.
    if (isPhasingOn())
    {
      emitPhaseSplit(i);
    }

    // positive:  s > 0 /\ t >= 0  =>  exp(s, t) > 0
    Node sgt0  = nm->mkNode(Kind::GT,  s, d_zero);
    Node tgeq0 = nm->mkNode(Kind::GEQ, t, d_zero);
    Node igt0  = nm->mkNode(Kind::GT,  i, d_zero);
    conj.push_back(nm->mkNode(Kind::IMPLIES,
                                nm->mkNode(Kind::AND, sgt0, tgeq0),
                                igt0));

    // non-negative:  s >= 0  =>  exp(s, t) >= 0
    //
    // The sign half of `positive`, with NO constraint on t -- which is what
    // makes it worth stating separately, since `positive` says nothing at all
    // once t < 0. For s >= 0 and t < 0 the value is 0 (s = 0 or s >= 2) or 1
    // (s = 1), never negative; for t >= 0 a non-negative base has a
    // non-negative power. Cheap and linear, so it is emitted unconditionally
    // alongside the other baseline axioms rather than behind a lemma token.
    // Note it is NOT redundant given `positive`: the two together still leave
    // s < 0 unconstrained, which is correct -- exp(-2,3) is negative.
    conj.push_back(nm->mkNode(Kind::IMPLIES,
                              nm->mkNode(Kind::GEQ, s, d_zero),
                              nm->mkNode(Kind::GEQ, i, d_zero)));

    // even:  s mod 2 = 0 /\ t >= 1  =>  exp(s, t) mod 2 = 0
    Node smod2 = nm->mkNode(Kind::INTS_MODULUS, s, d_two);
    Node imod2 = nm->mkNode(Kind::INTS_MODULUS, i, d_two);
    Node sEven = nm->mkNode(Kind::EQUAL, smod2, d_zero);
    Node tgeq1 = nm->mkNode(Kind::GEQ,  t, d_one);
    Node iEven = nm->mkNode(Kind::EQUAL, imod2, d_zero);
    conj.push_back(nm->mkNode(Kind::IMPLIES,
                                nm->mkNode(Kind::AND, sEven, tgeq1),
                                iEven));

    // odd:  s mod 2 = 1 /\ t >= 0  =>  exp(s, t) mod 2 = 1
    //
    // The parity mirror of `even`, and emitted unconditionally alongside it.
    // Two differences from `even` are deliberate:
    //
    //   * t >= 0 rather than t >= 1. `even` must exclude t = 0 because
    //     exp(s,0) = 1 is odd; the odd case has no such exception, since 1 is
    //     exactly what this concludes.
    //   * t >= 0 is required, though. For t < 0 and |s| >= 3 odd the value is
    //     0, which is even -- e.g. exp(3,-1) = 0. Only |s| = 1 escapes that,
    //     and those two cases are already pinned by bnd4 and neg-one, so
    //     adding them back as a disjunct would buy nothing.
    //
    // INTS_MODULUS is Euclidean here, so `s mod 2 = 1` covers negative odd
    // bases too: (-3) mod 2 = 1, and exp(-3,3) = -27 with (-27) mod 2 = 1.
    // Checked exhaustively over s, t in [-15,15].
    Node sOdd = nm->mkNode(Kind::EQUAL, smod2, d_one);
    Node iOdd = nm->mkNode(Kind::EQUAL, imod2, d_one);
    conj.push_back(nm->mkNode(Kind::IMPLIES,
                              nm->mkNode(Kind::AND, sOdd, tgeq0),
                              iOdd));
    
    // div1:  s >= 2 /\ t >= 0  =>  t div exp(s, t) = 0
    Node sgeq2 = nm->mkNode(Kind::GEQ, s, d_two);
    Node tDivI = nm->mkNode(Kind::INTS_DIVISION, t, i);
    conj.push_back(nm->mkNode(Kind::IMPLIES,
                                nm->mkNode(Kind::AND, sgeq2, tgeq0),
                                nm->mkNode(Kind::EQUAL, tDivI, d_zero)));

    // div2:  s >= 2 /\ t >= 2  =>  s div exp(s, t) = 0
    Node tgeq2 = nm->mkNode(Kind::GEQ, t, d_two);
    Node sDivI = nm->mkNode(Kind::INTS_DIVISION, s, i);
    conj.push_back(nm->mkNode(Kind::IMPLIES,
                                nm->mkNode(Kind::AND, sgeq2, tgeq2),
                                nm->mkNode(Kind::EQUAL, sDivI, d_zero)));


    // zero: t = o =>  exp(s, t) = 1
    Node teq1 = nm->mkNode(Kind::EQUAL, t, d_zero);
    conj.push_back(nm->mkNode(Kind::IMPLIES,
                                teq1,
                                i.eqNode(d_one)));

    // one: s = 1 =>  exp(s, t) = 1
    Node seq1   = nm->mkNode(Kind::EQUAL, s, d_one);
    conj.push_back(nm->mkNode(Kind::IMPLIES,
                                seq1,
                                i.eqNode(d_one)));
    
    // neg -1 (s = -1 /\ t < 0 => exp(s,t) = exp(s,-t)) used to be emitted
    // here, once per EXP term. It now lives in the full-refinement loop
    // instead -- see checkNegOneRefine. The move matters because the lemma
    // introduces the mirror term exp(s,-t): as an initial-refine axiom that
    // happened for EVERY exp term whether or not any model needed it, and
    // each mirror is itself an EXP term that then gets its own axiom batch.
    Node tlt0 = nm->mkNode(Kind::LT, t, d_zero);
    
    // neg 0: s = 0 /\ t < 0 =>  exp(s, t) = (div 1 0)
    // Node onediv0 = nm->mkNode(Kind::INTS_DIVISION, d_one, d_zero);
    // conj.push_back(nm->mkNode(Kind::IMPLIES,
    //                             nm->mkNode(Kind::AND, tlt0, sgt0),
    //                             i.eqNode(onediv0)));
    
    // neg |s| > 1:  t < 0 /\ (s > 1 \/ s < -1)  =>  exp(s, t) = 0
    Node sgt1    = nm->mkNode(Kind::GT, s, d_one);
    Node sltm1   = nm->mkNode(Kind::LT, s, d_negone);
    Node absGt1  = nm->mkNode(Kind::OR, sgt1, sltm1);
    conj.push_back(nm->mkNode(Kind::IMPLIES,
                                nm->mkNode(Kind::AND, tlt0, absGt1),
                                i.eqNode(d_zero)));

    // neg reciprocal:  t < 0  =>  exp(s, t) = 1 div exp(s, -t)
    // Relates a power to the reciprocal of its negated-exponent mirror. Only
    // sound under integer div when t < 0 (both sides collapse to 0/1); for
    // t >= 0 it would force exp(s,t) = 1 div 0 = 0, so it is guarded here.
    // Emitted only when --arith-exp-neg-recip=init (default off; the 'refine'
    // mode emits it from checkFullRefine instead).
    if (options().arith.expNegRecipMode
        == options::ExpNegRecipMode::INIT)
    {
      Node mirror =
          nm->mkNode(Kind::EXP, s, nm->mkNode(Kind::NEG, t));
      Node recip = nm->mkNode(Kind::INTS_DIVISION, d_one, mirror);
      conj.push_back(nm->mkNode(Kind::IMPLIES, tlt0, i.eqNode(recip)));
    }

    // Parity of the base -1 (--arith-exp-negone-parity):
    //   s = -1  =>  ite(t mod 2 = 0, exp(s,t) = 1, exp(s,t) = -1)
    //
    // The existing `neg-one` full-refine lemma only mirrors exp(-1,t) onto
    // exp(-1,-t), and `bnd4`/the range axioms only bound the value; nothing
    // pins WHICH of -1 and 1 it is. That is the whole difficulty in the LoAT
    // size0* families, where (-1)^t is the only exponential present and every
    // other power is polynomial: with the value pinned, a case split on
    // t mod 2 leaves an ordinary polynomial problem in each branch.
    //
    // Sound for every integer exponent. For t >= 0 this is the definition of
    // (-1)^t; for t < 0, `**` gives 1 div exp(s,-t), which is 1 div (+-1) and
    // so again +-1, and Euclidean `t mod 2` has the same value at t and -t.
    // Introduces no new EXP term, so unlike `neg-one` it costs nothing beyond
    // the mod term itself.
    // Either spelling turns it on: the standalone boolean, or the
    // 'negone-parity' token on --arith-exp-lemmas.
    if (options().arith.expNegOneParity || lselNegOne.has("negone-parity"))
    {
      Node tEven = nm->mkNode(
          Kind::EQUAL, nm->mkNode(Kind::INTS_MODULUS, t, d_two), d_zero);
      conj.push_back(nm->mkNode(
          Kind::IMPLIES,
          nm->mkNode(Kind::EQUAL, s, d_negone),
          nm->mkNode(Kind::ITE, tEven, i.eqNode(d_one), i.eqNode(d_negone))));
    }

    // Predecessor chain (--arith-exp-halving=N):
    //   t >= 1        =>  exp(s, t)   = s * exp(s, t-1)
    //   t - 1 >= 1    =>  exp(s, t-1) = s * exp(s, t-2)   (and so on, N steps)
    //
    // Sound for every base: the guard keeps the smaller exponent non-negative,
    // where `**` agrees with ordinary exponentiation. What the lemma really
    // buys is the TERM exp(s, t-1), linked to exp(s, t) by an equation. In the
    // PBV-to-int encoding the width power 2^k is ground while the sign-bit
    // threshold 2^(k-1) appears only under a quantifier, so nothing at ground
    // level ties the two together and the arithmetic solver cannot pin down
    // the translations of `min`/`max`. One step of this chain supplies exactly
    // that missing equation.
    //
    // Introducing terms is also why the chain has to be bounded: each new
    // exp(s, t-i) is itself an EXP term that reaches d_exps on a later round,
    // so the terms recorded in d_halveIntroduced are skipped here.
    // Either spelling turns it on: the standalone --arith-exp-halving=N, or
    // the 'halving' token on --arith-exp-lemmas, which means depth 1 (the
    // documented typical use). A depth given explicitly wins, so the token
    // never shortens a chain the user asked to be longer.
    uint64_t halveDepth = options().arith.expHalvingDepth;
    if (halveDepth == 0 && lselNegOne.has("halving"))
    {
      halveDepth = 1;
    }
    if (halveDepth > 0
        && d_halveIntroduced.find(i) == d_halveIntroduced.end())
    {
      Node cur = i;
      Node curT = t;
      for (uint64_t d = 0; d < halveDepth; ++d)
      {
        Node prevT = nm->mkNode(Kind::SUB, curT, d_one);
        Node prev = nm->mkNode(Kind::EXP, s, prevT);
        d_halveIntroduced.insert(prev);
        d_halveIntroduced.insert(rewrite(prev));
        conj.push_back(nm->mkNode(Kind::IMPLIES,
                                  nm->mkNode(Kind::GEQ, curT, d_one),
                                  cur.eqNode(nm->mkNode(Kind::MULT, s, prev))));
        cur = prev;
        curT = prevT;
      }
    }

    // SwInE static lemma families (Frohn & Giesl), gated by
    // --arith-exp-lemmas. Symmetry and bounding need no model, so they are
    // emitted here as initial-refine axioms.
    {
      // Static (non-model) families emitted as initial-refine axioms. Symmetry
      // is NOT here; it is emitted only in the full-refine loop (see
      // checkSymmetryRefine).
      ExpFeatureSet lsel(options().arith.expLemmasMode, ExpFeatureAxis::LEMMAS);
      // 'init' and 'both' emit the static axiom batch here; 'refine' emits
      // only from the refinement loop, filtered by what the candidate model
      // actually violates; 'none' emits nothing.
      options::ExpBoundingMode bmode = getBoundingMode(lsel);
      if (bmode == options::ExpBoundingMode::INIT
          || bmode == options::ExpBoundingMode::BOTH)
      {
        addBoundingLemmas(i, conj);
      }
    }

    Node lem = nm->mkAnd(conj);
    Trace("exp-lemma") << "ExpSolver::Lemma: " << lem << " ; INIT_REFINE"
                        << std::endl;
    addExpLemma(lem, InferenceId::ARITH_NL_EXP_INIT_REFINE);
  }
}


// void ExpSolver::sortExpsBasedOnModel() {}

bool ExpSolver::isPhasingOn() const
{
  // Phasing predates the --arith-exp-lemmas list and kept its own boolean;
  // the 'phasing' token is the second spelling, and either turns it on. It is
  // 'all' implies it, since on the lemma axis 'all' means every selection
  // without exception -- phasing included, though it is a search strategy
  // rather than a lemma family.
  return options().arith.expPhasing
         || ExpFeatureSet(options().arith.expLemmasMode, ExpFeatureAxis::LEMMAS)
                .has("phasing");
}

options::ExpBoundingMode ExpSolver::getBoundingMode(
    const ExpFeatureSet& lsel) const
{
  // --arith-exp-bounding and the 'bounding' token of --arith-exp-lemmas are
  // two spellings of the same switch. An explicit --arith-exp-bounding always
  // wins, so it can both place the family (init/refine/both) without naming
  // the token and switch it off ('none') despite the token.
  if (options().arith.expBoundingModeWasSetByUser)
  {
    return options().arith.expBoundingMode;
  }
  // Otherwise the token decides: naming it selects the strongest placement,
  // omitting it leaves the family off entirely.
  return lsel.has("bounding") ? options::ExpBoundingMode::BOTH
                              : options::ExpBoundingMode::NONE;
}

void ExpSolver::checkFullRefine() {
    Trace("exp-check") << "ExpSolver::checkFullRefine" << std::endl;
  NodeManager* nm = nodeManager();
  // Phasing (Alg. 3 lines 11-15): an unsat-phase counterexample is discarded
  // without computing any refinement lemmas -- raising the bound and going
  // back to the sat-phase is the whole of the round.
  if (isPhasingOn() && checkPhase())
  {
    return;
  }
  // SwInE model-based lemma families gated by --arith-exp-lemmas.
  ExpFeatureSet lsel(options().arith.expLemmasMode, ExpFeatureAxis::LEMMAS);
  bool primeOn = lsel.has("prime");
  bool indOn = lsel.has("induction");
  bool interpOn = lsel.has("interpolation");
  // The 'symmetry' mode -- and the 'all'/'pbv' aggregates -- emit the
  // symmetry lemmas here (in the full-refinement loop), for model-violating
  // terms.
  bool symRefineOn = lsel.has("symmetry");
  // The 'compose' mode emits the composition lemma in the full-refinement loop
  // for model-violating nested EXP terms.
  bool composeOn = lsel.has("compose");
  // Where the bnd2/bnd3/bnd5 family goes, resolved once for the whole round.
  options::ExpBoundingMode boundingMode = getBoundingMode(lsel);
  // General monotonicity (Frohn & Giesl `mon`). It subsumes the two same-base
  // pair lemmas below, so those are suppressed while it is on, and it runs as
  // its own scan over ALL pairs -- the loop below only ever reaches a pair
  // whose first element is itself model-violating, which would hide exactly
  // the cross-base cases `mon` exists for.
  // Selectable either as the 'mon' token of --arith-exp-lemmas or with the
  // standalone --arith-exp-mon-general boolean; the two are OR-ed. 'all' and
  // 'pbv' both imply it.
  bool genMon = options().arith.expMonGeneral || lsel.has("mon");
  if (genMon)
  {
    checkMonotonicityRefine();
  }
  // Guarded same-base fusion. Like monotonicity this is its own scan over ALL
  // pairs rather than a step inside the violating-term loop below: the pair
  // that closes the goal need not have a violating term as its first element.
  bool fuseModel = lsel.has("fuse-model");
  if (lsel.has("fuse") || fuseModel)
  {
    checkFuseRefine(fuseModel);
  }
  // Same-exponent fusion. Its own scan over all pairs, for the same reason.
  if (lsel.has("fuse-base"))
  {
    checkFuseBaseRefine();
  }
//   sortPow2sBasedOnModel();
  // add lemmas for each pow2 term
  for (uint64_t i = 0, size = d_exps.size(); i < size; i++)
  {
    Node n = d_exps[i];
    Node valExpxAbstract = d_model.computeAbstractModelValue(n);
    Node valExpxConcrete = d_model.computeConcreteModelValue(n);

    Node s = n[0];
    Node t = n[1];
    Node valS = d_model.computeConcreteModelValue(s);
    Node valt = d_model.computeConcreteModelValue(t);

    // A concrete value can fail to fold to a constant: a nested exponent such
    // as 2^(2^k - ...) whose intermediate value is too large for the rewriter
    // to expand stays symbolic. Reading getConst on such a node is undefined
    // (it crashed in a subsolver whose models wander into huge exponents), so
    // a term without constant values is skipped this round.
    if (!valS.isConst() || !valt.isConst() || !valExpxAbstract.isConst())
    {
      Trace("exp-check") << "* " << n << ": non-constant model value, skip"
                         << std::endl;
      continue;
    }
    Integer model_s = valS.getConst<Rational>().getNumerator();
    Integer model_t = valt.getConst<Rational>().getNumerator();
    Integer expx = valExpxAbstract.getConst<Rational>().getNumerator();

    if (TraceIsOn("exp-check"))
    {
      Trace("exp-check") << "* " << n << ", value = " << valExpxAbstract
                          << std::endl;
      Trace("exp-check") << "  actual " << valExpxConcrete << " = "
                          << valExpxConcrete << std::endl;
    }
    if (valExpxAbstract == valExpxConcrete)
    {
      Trace("exp-check") << "...already correct" << std::endl;
      continue;
    }

    // --arith-exp-value-only: nothing but the evaluated point.
    if (options().arith.expValueOnly)
    {
      Node vlem = valueBasedLemma(n);
      addExpLemma(
          vlem, InferenceId::ARITH_NL_POW2_VALUE_REFINE, nullptr, true);
      continue;
    }

    // neg-one, moved here from initial refine. Emitted only when the model
    // satisfies the antecedent, so the mirror term is introduced only for the
    // terms a candidate model actually points at.
    checkNegOneRefine(n, model_s, model_t);

    // add monotinicity lemmas
    for (uint64_t j = i + 1; j < size; j++)
    {
      Node m = d_exps[j];
      Node sy = m[0];
      Node ty = m[1];
      Node valSY = d_model.computeConcreteModelValue(sy);
      Node valTY = d_model.computeConcreteModelValue(ty);
      if (!valSY.isConst() || !valTY.isConst())
      {
        continue;  // see the guard above
      }
      Integer model_sy = valSY.getConst<Rational>().getNumerator();
      Integer model_ty = valTY.getConst<Rational>().getNumerator();
      // Abstract model value of m = exp(s_y, t_y). This must be m's own value
      // (not n's): the guards below only emit a pairwise lemma when BOTH
      // instances' model values together violate it. (Previously this read
      // valExpxAbstract, i.e. expx, so every such guard was trivially true and
      // the lemmas fired even when the model already satisfied them.)
      Node valExpyAbstract = d_model.computeAbstractModelValue(m);
      if (!valExpyAbstract.isConst())
      {
        continue;
      }
      Integer expy = valExpyAbstract.getConst<Rational>().getNumerator();

      // monotonicity: 0 <= s_x /\ s_x = s_y /\ 0 <= t_x /\ t_x < t_y => exp(s_x, t_x) < exp(s_y,t_y)
      if (!genMon && model_s >= 0  && model_t >= 0 && model_s == model_sy && model_t < model_ty && expy <= expx)
      {
        Node sxgeq0 = nm->mkNode(Kind::LEQ, d_zero, n[0]);
        Node txgeq0 = nm->mkNode(Kind::LEQ, d_zero, n[1]);
        Node sxgeqsy = nm->mkNode(Kind::EQUAL, n[0], m[0]);
        Node tx_lt_ty = nm->mkNode(Kind::LT, n[1], m[1]);
        Node assumption_pos = nm->mkNode(Kind::AND, sxgeq0, txgeq0);
        Node assumption_xgt = nm->mkNode(Kind::AND, tx_lt_ty, sxgeqsy);
        Node assumption = nm->mkNode(Kind::AND, assumption_pos, assumption_xgt);
        Node conclusion = nm->mkNode(Kind::LT, n, m);
        Node lem = nm->mkNode(Kind::IMPLIES, assumption, conclusion);
        addExpLemma(
            lem, InferenceId::ARITH_NL_EXP_MONOTONE_REFINE, nullptr, true);
      }
      // monotonicity: 0 <= s_x /\ s_x = s_y /\ 0 <= t_y /\ t_y < t_x => exp(s_x, t_x) > exp(s_y,t_y)
      else if (!genMon && model_s >= 0 && model_ty >= 0 && model_s == model_sy && model_t > model_ty && expy >= expx)
      {
        Node sxgeq0 = nm->mkNode(Kind::LEQ, d_zero, n[0]);
        Node tygeq0 = nm->mkNode(Kind::LEQ, d_zero, m[1]);
        Node sxgeqsy = nm->mkNode(Kind::EQUAL, n[0], m[0]);
        Node ty_lt_tx = nm->mkNode(Kind::LT, m[1], n[1]);
        Node assumption_pos = nm->mkNode(Kind::AND, sxgeq0, tygeq0);
        Node assumption_xgt = nm->mkNode(Kind::AND, ty_lt_tx, sxgeqsy);
        Node assumption = nm->mkNode(Kind::AND, assumption_pos, assumption_xgt);
        Node conclusion = nm->mkNode(Kind::LT, m, n);
        Node lem = nm->mkNode(Kind::IMPLIES, assumption, conclusion);
        addExpLemma(
            lem, InferenceId::ARITH_NL_EXP_MONOTONE_REFINE, nullptr, true);
      }
      // DOUBLING: for adjacent EXP exponents with a common base,
      // s_x = s_y /\ t_y = t_x + 1 => exp(s_y, t_y) = s_x * exp(s_x, t_x).
      // Cheap algebraic successor relation that the bare monotonicity lemma
      // above does not give. Gated by --nl-ext-exp-doubling (off by default).
      if (options().arith.nlExtExpDoubling
          && model_s == model_sy
          && model_t >= 0 && model_ty == model_t + 1)
      {
        // skip if the model already agrees: exp(s_y,t_y) = s_x * exp(s_x,t_x)
        if (expy != expx * model_s)
        {
          Node sxEqSy = nm->mkNode(Kind::EQUAL, n[0], m[0]);
          Node tySucc = nm->mkNode(
              Kind::EQUAL, m[1], nm->mkNode(Kind::ADD, n[1], d_one));
          Node assumDbl = nm->mkNode(Kind::AND, sxEqSy, tySucc);
          Node sxTimesN = nm->mkNode(Kind::MULT, n[0], n);
          Node conclDbl = nm->mkNode(Kind::EQUAL, m, sxTimesN);
          Node dblLem = nm->mkNode(Kind::IMPLIES, assumDbl, conclDbl);
          addExpLemma(
              dblLem, InferenceId::ARITH_NL_EXP_INDUCTION_REFINE, nullptr,
              true);
        }
      }
      {
        // Induction lemmas for EXP (base exp(s,0)=1 and step
        // t>=1 => exp(s,t) = s*exp(s,t-1)), always emitted.
        // Induction Lemma: 2 <= s_x /\ s_x = s_y /\ 0 <= t_x /\ t_x < t_y => exp(s_x, t_x) * s_x <= exp(s_y,t_y)
        if (model_s >= 2 && model_t >= 0 && model_s == model_sy && model_t < model_ty && expx * model_s > expy) {
          Node sxgeq2 = nm->mkNode(Kind::LEQ, d_two, n[0]);
          Node txgeq0 = nm->mkNode(Kind::LEQ, d_zero, n[1]);
          Node sxgeqsy = nm->mkNode(Kind::EQUAL, n[0], m[0]);
          Node tx_lt_ty = nm->mkNode(Kind::LT, n[1], m[1]);
          Node assumption_pos = nm->mkNode(Kind::AND, sxgeq2, txgeq0);
          Node assumption_xgt = nm->mkNode(Kind::AND, tx_lt_ty, sxgeqsy);
          Node assumption = nm->mkNode(Kind::AND, assumption_pos, assumption_xgt);
          Node xmulsx = nm->mkNode(Kind::MULT, n, n[0]);
          Node conclusion = nm->mkNode(Kind::LEQ, xmulsx, m);
          Node lem = nm->mkNode(Kind::IMPLIES, assumption, conclusion);
          addExpLemma(
              lem, InferenceId::ARITH_NL_EXP_INDUCTION_REFINE, nullptr, true);
        }
        // Induction Lemma: 2 <= s_x /\ s_x = s_y /\ 0 <= t_y /\ t_x > t_y => exp(s_x, t_x) >= exp(s_y,t_y) * s_y
        if (model_s >= 2 && model_ty >= 0 && model_s == model_sy && model_t > model_ty && expx < expy * model_sy) {
          Node sxgeq2 = nm->mkNode(Kind::LEQ, d_two, n[0]);
          Node tygeq0 = nm->mkNode(Kind::LEQ, d_zero, m[1]);
          Node sxgeqsy = nm->mkNode(Kind::EQUAL, n[0], m[0]);
          Node ty_lt_tx = nm->mkNode(Kind::LT, m[1], n[1]);
          Node assumption_pos = nm->mkNode(Kind::AND, sxgeq2, tygeq0);
          Node assumption_xgt = nm->mkNode(Kind::AND, ty_lt_tx, sxgeqsy);
          Node assumption = nm->mkNode(Kind::AND, assumption_pos, assumption_xgt);
          Node ymulsy = nm->mkNode(Kind::MULT, m, m[0]);
          Node conclusion = nm->mkNode(Kind::LEQ, ymulsy, n);
          Node lem = nm->mkNode(Kind::IMPLIES, assumption, conclusion);
          addExpLemma(
              lem, InferenceId::ARITH_NL_EXP_INDUCTION_REFINE, nullptr, true);
        }
      }
      // SwInE induction lemma (equality unrolling by the model exponent gap).
      if (indOn)
      {
        checkInductionLemma(n, m, model_s, model_t, model_sy, model_ty);
      }
    }

    // Symmetry lemmas emitted in the full-refine loop for this model-violating
    // term, when the 'symmetry' mode is set. Only the lemmas whose
    // antecedent holds in the model are emitted.
    if (symRefineOn)
    {
      checkSymmetryRefine(n, model_t);
    }

    // Compose lemma in the full-refine loop for this model-violating nested
    // EXP term, when the 'compose' mode is set.
    if (composeOn)
    {
      checkComposeRefine(n);
    }

    // SwInE prime and interpolation lemmas (per relevant, model-violating
    // term). Gated by --arith-exp-lemmas.
    if (primeOn)
    {
      checkPrimeLemma(n, model_s, expx);
    }
    if (interpOn)
    {
      checkInterpolationLemma(n, model_s, model_t, expx);
    }

    // Bounding as a live refinement family (--arith-exp-bounding=refine|both):
    // only the bnd lemmas this candidate model actually violates.
    if (boundingMode == options::ExpBoundingMode::REFINE
        || boundingMode == options::ExpBoundingMode::BOTH)
    {
      addBoundingRefine(n, model_s, model_t, expx);
    }

    // bound: s >= 2 /\ v >= 7 /\ v = t => exp(s,t) > vt + v^2
    if (model_s >= 2 && model_t >= 7 && expx <= model_t * model_t * 2)
    {
      Node d_seven = nm->mkConstInt(Rational(7));
      Node sge2    = nm->mkNode(Kind::GEQ, s, d_two);
      Node vge7 = nm->mkNode(Kind::GEQ, valt, d_seven);
      Node tgev = nm->mkNode(Kind::GEQ, n[1], valt);
      Node assumption = nm->mkNode(Kind::AND, sge2, vge7, tgev);
      Node vt = nm->mkNode(Kind::MULT, valt, n[1]);
      Node v_squar = nm->mkNode(Kind::MULT, valt, valt);
      Node vt_plus_v_squar = nm->mkNode(Kind::ADD, vt, v_squar);
      Node conclusion = nm->mkNode(Kind::GT, n, vt_plus_v_squar);
      Node lem = nm->mkNode(Kind::IMPLIES, assumption, conclusion);
      addExpLemma(lem,
                           InferenceId::ARITH_NL_EXP_BOUND_CASE_REFINE,
                           nullptr,
                           true);
    }



    // neg reciprocal:  t < 0  =>  exp(s, t) = 1 div exp(s, -t)
    // Only sound under integer div when t < 0 (both sides collapse to 0/1);
    // for t >= 0 it would force exp(s,t) = 1 div 0 = 0, so it is guarded here.
    // Emitted when --arith-exp-neg-recip=refine (default off; the 'init'
    // mode emits it once per term from checkInitialRefine instead), or when
    // the 'neg-recip' token is on --arith-exp-lemmas -- which 'exp-full'
    // selects, and which is the same refine placement. The two are OR-ed.
    if (options().arith.expNegRecipMode == options::ExpNegRecipMode::REFINE
        || lsel.has("neg-recip"))
    {
      Node tlt0 = nm->mkNode(Kind::LT, t, d_zero);
      Node negT = nm->mkNode(Kind::NEG, t);
      Node mirror = nm->mkNode(Kind::EXP, s, negT);
      Node recip = nm->mkNode(Kind::INTS_DIVISION, d_one, mirror);
      Node negRecipLem = nm->mkNode(Kind::IMPLIES, tlt0, n.eqNode(recip));
      addExpLemma(negRecipLem,
                           InferenceId::ARITH_NL_EXP_INIT_REFINE,
                           nullptr,
                           true);
    }

    // this is the most naive model-based schema based on model values
    Node lem = valueBasedLemma(n);
    Trace("pow2-lemma") << "Pow2Solver::Lemma: " << lem << " ; VALUE_REFINE"
                        << std::endl;
    // send the value lemma
    addExpLemma(
        lem, InferenceId::ARITH_NL_POW2_VALUE_REFINE, nullptr, true);
    }
}

Node ExpSolver::valueBasedLemma(Node i) {
  Assert(i.getKind() == Kind::EXP);
  Node s = i[0];
  Node t = i[1];

  Node valS = d_model.computeConcreteModelValue(s);
  Node valT = d_model.computeConcreteModelValue(t);

  NodeManager* nm = nodeManager();
  Node valC = nm->mkNode(Kind::EXP, valS, valT);
  valC = rewrite(valC);

  Node assum = nm->mkNode(Kind::AND, {s.eqNode(valS), t.eqNode(valT)});
  return nm->mkNode(Kind::IMPLIES, {assum, i.eqNode(valC)});
}

// ============================================================================
// SwInE lemma families (Frohn & Giesl, "Satisfiability Modulo Exponential
// Integer Arithmetic"). All lemmas below are EIA-valid; the model values are
// only used to *select* which valid lemma to emit. Under EIA semantics
// exp(s,t) = s^|t|.
// ============================================================================

void ExpSolver::checkMonotonicityRefine()
{
  // General monotonicity, Frohn & Giesl Sect. 4.2.2 (`mon`):
  //
  //   s2 >= s1 > 1 /\ t2 >= t1 > 0 /\ (s2 > s1 \/ t2 > t1)
  //     =>  exp(s2,t2) > exp(s1,t1)
  //
  // We emit a slightly stronger form that also covers t1 = 0:
  //
  //   2 <= s1 /\ s1 <= s2 /\ 0 <= t1 /\ t1 <= t2 /\ 1 <= t2
  //            /\ (s1 < s2 \/ t1 < t2)
  //     =>  exp(s1,t1) < exp(s2,t2)
  //
  // Validity. Every exponent in the antecedent is non-negative, and on t >= 0
  // cvc5's SMT-LIB `**` agrees with ordinary exponentiation, so the paper's
  // argument carries over verbatim. If t1 = 0 the left side is 1 while the
  // right side is s2^t2 >= 2^1 > 1. Otherwise s1^t1 <= s2^t1 <= s2^t2, strict
  // in the first step when s1 < s2 (as t1 >= 1) and in the second when
  // t1 < t2 (as s2 >= 2); the disjunct guarantees at least one of those.
  //
  // This subsumes the two same-base pair lemmas in checkFullRefine, which are
  // the s1 = s2 instances, and unlike them it relates powers with DIFFERENT
  // bases -- the case the paper needs for e.g. 1<x<y /\ 0<z /\ exp(x,z)<exp(y,z).
  NodeManager* nm = nodeManager();

  // Model snapshot: base, exponent and (abstract) value of every EXP term.
  struct MonPoint
  {
    Node n;
    Integer s;
    Integer t;
    Integer v;
  };
  std::vector<MonPoint> pts;
  pts.reserve(d_exps.size());
  for (const Node& e : d_exps)
  {
    Node vs = d_model.computeConcreteModelValue(e[0]);
    Node vt = d_model.computeConcreteModelValue(e[1]);
    Node ve = d_model.computeAbstractModelValue(e);
    if (!vs.isConst() || !vt.isConst() || !ve.isConst())
    {
      continue;
    }
    pts.push_back({e,
                   vs.getConst<Rational>().getNumerator(),
                   vt.getConst<Rational>().getNumerator(),
                   ve.getConst<Rational>().getNumerator()});
  }

  for (size_t i = 0, size = pts.size(); i < size; i++)
  {
    for (size_t j = i + 1; j < size; j++)
    {
      const MonPoint& a = pts[i];
      const MonPoint& b = pts[j];
      // Orient the pair by the model: `lo` must be dominated by `hi` in BOTH
      // arguments. A pair the model does not order (one base larger, the other
      // exponent larger) satisfies no instance of `mon`, so it is skipped.
      const MonPoint* lo;
      const MonPoint* hi;
      if (a.s <= b.s && a.t <= b.t)
      {
        lo = &a;
        hi = &b;
      }
      else if (b.s <= a.s && b.t <= a.t)
      {
        lo = &b;
        hi = &a;
      }
      else
      {
        continue;
      }
      // The antecedent has to hold in the model, or the lemma cannot rule the
      // model out. s1 >= 2 and t1 >= 0 and t2 >= 1, ...
      if (lo->s < Integer(2) || lo->t.sgn() < 0 || hi->t < Integer(1))
      {
        continue;
      }
      // ... and the pair must differ somewhere, or the conclusion would be the
      // false claim exp(s,t) < exp(s,t).
      if (lo->s == hi->s && lo->t == hi->t)
      {
        continue;
      }
      // Only emit lemmas the model violates (Alg. 2 line 10/14).
      if (lo->v < hi->v)
      {
        continue;
      }
      Node s1 = lo->n[0], t1 = lo->n[1];
      Node s2 = hi->n[0], t2 = hi->n[1];
      Node ant = nm->mkNode(
          Kind::AND,
          {nm->mkNode(Kind::GEQ, s1, d_two),
           nm->mkNode(Kind::LEQ, s1, s2),
           nm->mkNode(Kind::GEQ, t1, d_zero),
           nm->mkNode(Kind::LEQ, t1, t2),
           nm->mkNode(Kind::GEQ, t2, d_one),
           nm->mkNode(Kind::OR,
                      nm->mkNode(Kind::LT, s1, s2),
                      nm->mkNode(Kind::LT, t1, t2))});
      Node lem = nm->mkNode(
          Kind::IMPLIES, ant, nm->mkNode(Kind::LT, lo->n, hi->n));
      Trace("exp-lemma") << "ExpSolver::Lemma: " << lem << " ; MON_GENERAL"
                         << std::endl;
      addExpLemma(
          lem, InferenceId::ARITH_NL_EXP_MONOTONE_REFINE, nullptr, true);
    }
  }
}

void ExpSolver::checkFuseRefine(bool byModel)
{
  // Guarded same-base fusion:
  //
  //   s1 = s2 /\ t1 >= 0 /\ t2 >= 0  =>  exp(s1,t1) * exp(s2,t2) = exp(s1,t1+t2)
  //
  // Frohn & Giesl (Sect. 4.1/4.3) reject the unguarded rewrite as unsound for
  // EIA, whose exp(s,t) is s^|t|: their right-hand side would have to read
  // exp(x,|y|+|z|). cvc5's Kind::EXP is SMT-LIB `**`, which on NON-NEGATIVE
  // exponents is ordinary exponentiation, so the guarded identity above is
  // valid here for every integer base, including s = 0 (0^0 = 1). It cannot be
  // a rewrite -- a rewrite carries no side condition -- so it is a lemma
  // family instead. Sect. 4.3 names the absence of this identity as the reason
  // their Alg. 2 does not terminate on
  //   x >= y >= 0 /\ exp(2,x) != exp(2,x-y)*exp(2,y).
  //
  // Only the non-term-introducing case is emitted: the fused term must already
  // be an EXP term of the current problem, or rewrite to a constant. The
  // lemma then relates terms that all exist, adds nothing to the term graph,
  // and cannot diverge -- which is exactly the case that closes the example
  // above, where (x-y)+y normalizes to x and exp(2,x) is already present.
  NodeManager* nm = nodeManager();

  struct FusePoint
  {
    Node n;
    Integer s;
    Integer t;
    Integer v;
  };
  std::vector<FusePoint> pts;
  pts.reserve(d_exps.size());
  for (const Node& e : d_exps)
  {
    Node vs = d_model.computeConcreteModelValue(e[0]);
    Node vt = d_model.computeConcreteModelValue(e[1]);
    Node ve = d_model.computeAbstractModelValue(e);
    if (!vs.isConst() || !vt.isConst() || !ve.isConst())
    {
      continue;
    }
    pts.push_back({e,
                   vs.getConst<Rational>().getNumerator(),
                   vt.getConst<Rational>().getNumerator(),
                   ve.getConst<Rational>().getNumerator()});
  }

  // The 'fuse-model' variant: the fused exponent is matched by its candidate
  // model value rather than syntactically, so the exponent equality becomes
  // part of the antecedent. Only existing terms are related.
  auto checkFuseByModel = [&](const std::vector<FusePoint>& ps,
                              const std::vector<const FusePoint*>& fs) {
    Integer tsum(0);
    Integer vprod(1);
    for (const FusePoint* f : fs)
    {
      tsum += f->t;
      vprod *= f->v;
    }
    for (const FusePoint& p : ps)
    {
      if (p.s != fs[0]->s || p.t != tsum || vprod == p.v)
      {
        continue;
      }
      bool isFactor = false;
      for (const FusePoint* f : fs)
      {
        isFactor = isFactor || p.n == f->n;
      }
      if (isFactor)
      {
        continue;
      }
      std::vector<Node> conj;
      std::vector<Node> exps;
      std::vector<Node> facs;
      for (const FusePoint* f : fs)
      {
        conj.push_back(f->n[0].eqNode(p.n[0]));
        conj.push_back(nm->mkNode(Kind::GEQ, f->n[1], d_zero));
        exps.push_back(f->n[1]);
        facs.push_back(f->n);
      }
      conj.push_back(p.n[1].eqNode(nm->mkNode(Kind::ADD, exps)));
      Node prod = nm->mkNode(Kind::MULT, facs);
      Node lem = nm->mkNode(
          Kind::IMPLIES, nm->mkNode(Kind::AND, conj), prod.eqNode(p.n));
      Trace("exp-lemma") << "ExpSolver::Lemma: " << lem << " ; FUSE_MODEL"
                         << std::endl;
      addExpLemma(lem, InferenceId::ARITH_NL_EXP_FUSE_REFINE, nullptr, true);
    }
  };

  for (size_t i = 0, size = pts.size(); i < size; i++)
  {
    // 'fuse-model' also pairs a term with itself, exp(s,t)^2 = exp(s,2t).
    for (size_t j = byModel ? i : i + 1; j < size; j++)
    {
      const FusePoint& a = pts[i];
      const FusePoint& b = pts[j];
      // The guard must HOLD in the candidate model (Alg. 2 line 10): same base,
      // both exponents non-negative.
      if (a.s != b.s || a.t.sgn() < 0 || b.t.sgn() < 0)
      {
        continue;
      }
      Node sum = rewrite(nm->mkNode(Kind::ADD, a.n[1], b.n[1]));
      Node fused = rewrite(nm->mkNode(Kind::EXP, a.n[0], sum));
      bool haveVal = false;
      Integer fusedVal;
      if (fused.isConst())
      {
        fusedVal = fused.getConst<Rational>().getNumerator();
        haveVal = true;
      }
      else
      {
        for (const FusePoint& p : pts)
        {
          if (p.n == fused)
          {
            fusedVal = p.v;
            haveVal = true;
            break;
          }
        }
      }
      // Decline the pair when the fused term is new: emitting it would grow
      // the term set, and the fused term would pair with the existing ones
      // again next round.
      if (!haveVal)
      {
        if (byModel)
        {
          checkFuseByModel(pts, {&a, &b});
        }
        continue;
      }
      // Only emit when the model VIOLATES the conclusion.
      if (a.v * b.v == fusedVal)
      {
        continue;
      }
      Node ant = nm->mkNode(Kind::AND,
                            {a.n[0].eqNode(b.n[0]),
                             nm->mkNode(Kind::GEQ, a.n[1], d_zero),
                             nm->mkNode(Kind::GEQ, b.n[1], d_zero)});
      Node prod = nm->mkNode(Kind::MULT, a.n, b.n);
      Node lem = nm->mkNode(Kind::IMPLIES, ant, prod.eqNode(fused));
      Trace("exp-lemma") << "ExpSolver::Lemma: " << lem << " ; FUSE"
                         << std::endl;
      addExpLemma(
          lem, InferenceId::ARITH_NL_EXP_FUSE_REFINE, nullptr, true);
    }
  }
  // 'fuse-model' also tries three factors, which is what relates e.g.
  // 2^(n*n) to 2^((n-1)*(n-1)) * 2^(n-1) * 2^n. The scan is cubic, so it is
  // skipped on large term sets.
  if (byModel && pts.size() <= 40)
  {
    for (size_t i = 0, size = pts.size(); i < size; i++)
    {
      for (size_t j = i; j < size; j++)
      {
        for (size_t k = j; k < size; k++)
        {
          const FusePoint& a = pts[i];
          const FusePoint& b = pts[j];
          const FusePoint& c = pts[k];
          // A zero exponent only yields the pair lemma again.
          if (a.s != b.s || a.s != c.s || a.t.sgn() <= 0 || b.t.sgn() <= 0
              || c.t.sgn() <= 0)
          {
            continue;
          }
          checkFuseByModel(pts, {&a, &b, &c});
        }
      }
    }
  }
}

void ExpSolver::checkNegOneRefine(Node n,
                                 const Integer& ms,
                                 const Integer& mt)
{
  // neg-one:  s = -1 /\ t < 0  =>  exp(s,t) = exp(s,-t)
  //
  // Valid because (-1)^|t| depends only on the parity of t, and |t| and -t
  // have the same parity -- so the two sides are the same element of {-1, 1}.
  //
  // This was an unconditional initial-refine axiom. It is a full-refinement
  // lemma now, guarded by the candidate model satisfying its antecedent
  // (Alg. 2 line 10), because it is one of the few axioms here that
  // INTRODUCES a term: exp(s,-t) is a fresh EXP term, which then collects its
  // own axiom batch and pairs with every other exp term in the pairwise
  // scans. Emitting it once per term up front paid that cost on every problem
  // containing any exponential; emitting it only for a model-violating term
  // whose model actually has s = -1 and t < 0 pays it almost never.
  if (ms != Integer(-1) || mt.sgn() >= 0)
  {
    return;
  }
  NodeManager* nm = nodeManager();
  Node s = n[0];
  Node t = n[1];
  Node mirror = nm->mkNode(Kind::EXP, s, nm->mkNode(Kind::NEG, t));
  Node lem = nm->mkNode(
      Kind::IMPLIES,
      nm->mkNode(Kind::AND,
                 nm->mkNode(Kind::EQUAL, s, d_negone),
                 nm->mkNode(Kind::LT, t, d_zero)),
      n.eqNode(mirror));
  Trace("exp-lemma") << "ExpSolver::Lemma: " << lem << " ; NEG_ONE"
                     << std::endl;
  addExpLemma(
      lem, InferenceId::ARITH_NL_EXP_INIT_REFINE, nullptr, true);
}

void ExpSolver::checkFuseBaseRefine()
{
  // Same-exponent fusion:
  //
  //   exp(s,a) * exp(t,a) = exp(s*t, a)
  //
  // UNGUARDED, and that is not an oversight: unlike the same-base `fuse` and
  // unlike `compose`, this identity survives negative exponents under `**`.
  // For a >= 0 it is the ordinary power law. For a < 0 every factor lies in
  // {-1, 0, 1}: exp(s,a) is 0 unless |s| = 1, and the product of the two sides
  // agrees case by case -- e.g. s = -1, t = 2, a = -1 gives (-1)*0 = 0 on the
  // left and exp(-2,-1) = 0 on the right. Checked exhaustively over
  // [-9,9]^3 and on 400k random points with |s|,|t| <= 40, |a| <= 25.
  //
  // As with checkFuseRefine, only the non-term-introducing case is emitted:
  // the fused term exp(s*t, a) must already be an EXP term of the problem or
  // rewrite to a constant. That keeps the term graph fixed and stops the
  // family from feeding itself new pairs each round.
  NodeManager* nm = nodeManager();

  struct Point
  {
    Node n;
    Integer s;
    Integer t;
    Integer v;
  };
  std::vector<Point> pts;
  pts.reserve(d_exps.size());
  for (const Node& e : d_exps)
  {
    Node vs = d_model.computeConcreteModelValue(e[0]);
    Node vt = d_model.computeConcreteModelValue(e[1]);
    Node ve = d_model.computeAbstractModelValue(e);
    if (!vs.isConst() || !vt.isConst() || !ve.isConst())
    {
      continue;
    }
    pts.push_back({e,
                   vs.getConst<Rational>().getNumerator(),
                   vt.getConst<Rational>().getNumerator(),
                   ve.getConst<Rational>().getNumerator()});
  }

  for (size_t i = 0, size = pts.size(); i < size; i++)
  {
    for (size_t j = i + 1; j < size; j++)
    {
      const Point& a = pts[i];
      const Point& b = pts[j];
      // Pair up on a COMMON EXPONENT, where fuse pairs on a common base. The
      // exponents need only agree in the candidate model; the emitted lemma
      // states that agreement as its antecedent.
      if (a.t != b.t)
      {
        continue;
      }
      Node prodBase = rewrite(nm->mkNode(Kind::MULT, a.n[0], b.n[0]));
      Node fused = rewrite(nm->mkNode(Kind::EXP, prodBase, a.n[1]));
      bool haveVal = false;
      Integer fusedVal;
      if (fused.isConst())
      {
        fusedVal = fused.getConst<Rational>().getNumerator();
        haveVal = true;
      }
      else
      {
        for (const Point& p : pts)
        {
          if (p.n == fused)
          {
            fusedVal = p.v;
            haveVal = true;
            break;
          }
        }
      }
      if (!haveVal)
      {
        continue;
      }
      // Only emit when the model VIOLATES the conclusion (Alg. 2 line 10).
      if (a.v * b.v == fusedVal)
      {
        continue;
      }
      Node lem = nm->mkNode(Kind::IMPLIES,
                            a.n[1].eqNode(b.n[1]),
                            nm->mkNode(Kind::MULT, a.n, b.n).eqNode(fused));
      Trace("exp-lemma") << "ExpSolver::Lemma: " << lem << " ; FUSE_BASE"
                         << std::endl;
      addExpLemma(
          lem, InferenceId::ARITH_NL_EXP_FUSE_REFINE, nullptr, true);
    }
  }
}

void ExpSolver::checkComposeRefine(Node n)
{
  // Lemmas for a model-violating nested term n = exp(exp(x,y),z).
  if (n[0].getKind() != Kind::EXP) return;
  NodeManager* nm = nodeManager();
  Node x = n[0][0];
  Node y = n[0][1];
  Node z = n[1];

  // Composition, GUARDED:
  //     y >= 0 /\ z >= 0  =>  exp(exp(x,y),z) = exp(x, y*z)
  //
  // The guard is not optional. The EIA reading (x^|y|)^|z| = x^|y*z| treats a
  // negative exponent as its absolute value; cvc5's EXP is SMT-LIB `**`, where
  // a negative exponent gives 1 div x^|t| instead. Unguarded the identity
  // fails as soon as an exponent is negative -- for x = y = z = -6 the left
  // side is exp(0,-6) = 0 while the right side is (-6)^36. On y, z >= 0 the
  // two readings agree and the identity is the ordinary power law; checked
  // exhaustively over [-9,9]^3. Note >= 0 rather than > 0: the y = 0 and
  // z = 0 cases are valid too (both sides are 1, resp. exp(x,0) = 1).
  Node yNonNeg = nm->mkNode(Kind::GEQ, y, d_zero);
  Node zNonNeg = nm->mkNode(Kind::GEQ, z, d_zero);
  Node yz = nm->mkNode(Kind::MULT, y, z);
  addExpLemma(
      nm->mkNode(Kind::IMPLIES,
                 nm->mkNode(Kind::AND, yNonNeg, zNonNeg),
                 n.eqNode(nm->mkNode(Kind::EXP, x, yz))),
      InferenceId::ARITH_NL_EXP_INIT_REFINE,
      nullptr,
      true);

  // The negative-inner-exponent case, which composition no longer covers:
  //     y < 0 /\ (x > 1 \/ x < -1) /\ z != 0  =>  exp(exp(x,y),z) = 0
  //
  // y < 0 with |x| > 1 makes the inner power 0 (that is the always-on neg-abs
  // axiom), and exp(0,z) is 0 for every z != 0. The z != 0 conjunct is needed:
  // at z = 0 the whole term is 1, not 0. Checked exhaustively over [-9,9]^3.
  Node yNeg = nm->mkNode(Kind::LT, y, d_zero);
  Node absXGt1 = nm->mkNode(Kind::OR,
                            nm->mkNode(Kind::GT, x, d_one),
                            nm->mkNode(Kind::LT, x, d_negone));
  Node zNZ = nm->mkNode(Kind::EQUAL, z, d_zero).notNode();
  addExpLemma(
      nm->mkNode(Kind::IMPLIES,
                 nm->mkNode(Kind::AND, yNeg, absXGt1, zNZ),
                 n.eqNode(d_zero)),
      InferenceId::ARITH_NL_EXP_INIT_REFINE,
      nullptr,
      true);
}

void ExpSolver::checkSymmetryRefine(Node n, const Integer& model_t)
{
  // Emit only the symmetry lemmas that can rule out the current model: a
  // conditional lemma whose antecedent is false in the model (wrong parity of
  // t) is already satisfied, so skip it. n is a model-violating term, so the
  // equality conclusions are falsified by the model.
  NodeManager* nm = nodeManager();
  Node s = n[0];
  Node t = n[1];
  Node expNegS = nm->mkNode(Kind::EXP, nm->mkNode(Kind::NEG, s), t);
  Node tEvenPred = nm->mkNode(
      Kind::EQUAL, nm->mkNode(Kind::INTS_MODULUS, t, d_two), d_zero);
  bool tEven = model_t.euclidianDivideRemainder(Integer(2)).isZero();
  if (tEven)
  {
    // sym1: divisible2(t) => exp(s,t) = exp(-s,t)
    addExpLemma(
        nm->mkNode(Kind::IMPLIES, tEvenPred, n.eqNode(expNegS)),
        InferenceId::ARITH_NL_EXP_INIT_REFINE, nullptr, true);
  }
  else
  {
    // sym2: ~divisible2(t) => exp(s,t) = -exp(-s,t)
    addExpLemma(
        nm->mkNode(Kind::IMPLIES,
                   tEvenPred.notNode(),
                   n.eqNode(nm->mkNode(Kind::NEG, expNegS))),
        InferenceId::ARITH_NL_EXP_INIT_REFINE, nullptr, true);
  }
  // NOTE: sym3 -- exp(s,t) = exp(s,-t), emitted unconditionally for a
  // model-violating term -- used to sit here behind an 'sym3' token. It is
  // UNSOUND under this solver's semantics: cvc5's EXP is SMT-LIB `**`, where a
  // negative exponent gives 1 div exp(s,-t) rather than the paper's s^|t|, so
  // for s = 2, t = 1 the lemma claims 2 = exp(2,-1) = 0. It has been removed
  // rather than left behind a flag. sym1 and sym2 above were checked against
  // `**` including negative and zero exponents and are sound; the sound mirror
  // relation is --arith-exp-neg-recip.
}

void ExpSolver::addBoundingLemmas(Node i, std::vector<Node>& conj)
{
  // bnd2: t=1               => exp(s,t) = s
  // bnd3: s=0 /\ t!=0       => exp(s,t) = 0   (forward only, see below)
  // bnd5: s>=2 /\ t>=2      => exp(s,t) >= s*s*(t-1)   (generalized; see below)
  // (bnd1 t=0=>exp=1 and bnd4 s=1=>exp=1 are already emitted unconditionally.)
  NodeManager* nm = nodeManager();
  Node s = i[0];
  Node t = i[1];
  conj.push_back(nm->mkNode(
      Kind::IMPLIES, nm->mkNode(Kind::EQUAL, t, d_one), i.eqNode(s)));
  Node sZero = nm->mkNode(Kind::EQUAL, s, d_zero);
  Node tNZ = nm->mkNode(Kind::EQUAL, t, d_zero).notNode();
  // bnd3, forward direction only. It was previously emitted here as the
  // equivalence (s = 0 /\ t != 0) <=> exp(s,t) = 0, which is UNSOUND under
  // cvc5's SMT-LIB `**`: the converse reads exp(s,t) = 0 => s = 0, but a
  // negative exponent gives exp(s,t) = 1 div exp(s,-t) = 0 for every |s| > 1,
  // so exp(2,-1) = 0 would derive 2 = 0. (It produced a wrong `unsat` on
  // s >= 2 /\ t = 1 /\ exp(s,t) != exp(s,-t), which is satisfiable.) The
  // forward direction is sound for every t, since (** 0 n) = 0 for n < 0 as
  // well as n > 0. addBoundingRefine emits the converse separately under the
  // guard t >= 0, which is where it is actually valid.
  conj.push_back(nm->mkNode(Kind::IMPLIES,
                            nm->mkNode(Kind::AND, sZero, tNZ),
                            nm->mkNode(Kind::EQUAL, i, d_zero)));
  // bnd5, generalized. The paper's form is
  //     s+t > 4 /\ s > 1 /\ t > 1  =>  exp(s,t) > s*t + 1
  // which is emitted here instead as
  //     s >= 2 /\ t >= 2           =>  exp(s,t) >= s*s*(t-1).
  //
  // Validity. For s >= 2 and t >= 2, `**` agrees with ordinary exponentiation,
  // and s^t = s^2 * s^(t-2) >= s^2 * 2^(t-2) >= s^2 * (t-1), the last step by
  // 2^(t-2) >= t-1 for t >= 2 (t=2 gives 1 >= 1, and doubling the left side
  // beats adding one to the right).
  //
  // Generality. On the paper's region (s,t > 1 and s+t > 4) one has
  // s^2*(t-1) > s*t+1 strictly, so this conclusion IMPLIES bnd5 there -- it is
  // a strict strengthening, not a trade. It also covers the cell bnd5 leaves
  // out, s = t = 2, where it gives the tight 4 >= 4. Both facts were checked
  // exhaustively over [2,200)^2.
  //
  // The conclusion is degree 3 rather than bnd5's degree 2, which is the cost;
  // it introduces no EXP term, since s*s is an ordinary product.
  Node sGe2 = nm->mkNode(Kind::GEQ, s, d_two);
  Node tGe2 = nm->mkNode(Kind::GEQ, t, d_two);
  Node genBound = nm->mkNode(Kind::MULT,
                             nm->mkNode(Kind::MULT, s, s),
                             nm->mkNode(Kind::SUB, t, d_one));
  conj.push_back(nm->mkNode(Kind::IMPLIES,
                            nm->mkNode(Kind::AND, sGe2, tGe2),
                            nm->mkNode(Kind::GEQ, i, genBound)));
}

void ExpSolver::addBoundingRefine(Node i,
                                  const Integer& ms,
                                  const Integer& mt,
                                  const Integer& mv)
{
  // The bounding lemmas of addBoundingLemmas, but emitted one at a time and
  // only when the candidate model violates them -- Frohn & Giesl's Bounding
  // kind under the Alg. 2 line 10 filter, rather than a static axiom batch.
  //
  // Each guard below is the model-side reading of the lemma it emits: the
  // antecedent must hold in the model and the conclusion must fail there, or
  // the lemma is already satisfied and is not a member of L.
  //
  // bnd1 (t=0 => exp=1) and bnd4 (s=1 => exp=1) are not here: they are emitted
  // unconditionally at initial refine in every mode, so by the time a model
  // exists they can no longer be violated.
  NodeManager* nm = nodeManager();
  Node s = i[0];
  Node t = i[1];
  const Integer one(1);
  // bnd2: t = 1 => exp(s,t) = s
  if (mt == one && mv != ms)
  {
    addExpLemma(nm->mkNode(Kind::IMPLIES,
                                    nm->mkNode(Kind::EQUAL, t, d_one),
                                    i.eqNode(s)),
                         InferenceId::ARITH_NL_EXP_BOUND_CASE_REFINE,
                         nullptr,
                         true);
  }
  Node sZero = nm->mkNode(Kind::EQUAL, s, d_zero);
  Node tNZ = nm->mkNode(Kind::EQUAL, t, d_zero).notNode();
  Node iZero = nm->mkNode(Kind::EQUAL, i, d_zero);
  // bnd3 forward: s = 0 /\ t != 0 => exp(s,t) = 0. Sound for every t under
  // SMT-LIB `**`, since (** 0 n) = 0 for n < 0 as well as for n > 0.
  if (ms.sgn() == 0 && mt.sgn() != 0 && mv.sgn() != 0)
  {
    addExpLemma(
        nm->mkNode(Kind::IMPLIES, nm->mkNode(Kind::AND, sZero, tNZ), iZero),
        InferenceId::ARITH_NL_EXP_BOUND_CASE_REFINE,
        nullptr,
        true);
  }
  // bnd3 converse, guarded by t >= 0: the paper's s^|t| vanishes only at
  // s = 0, but `**` also gives exp(s,t) = 0 for every t < 0 with |s| > 1, so
  // the unguarded equivalence would derive s = 0 from exp(2,-1) = 0.
  if (mt.sgn() >= 0 && mv.sgn() == 0 && !(ms.sgn() == 0 && mt.sgn() != 0))
  {
    addExpLemma(
        nm->mkNode(Kind::IMPLIES,
                   nm->mkNode(
                       Kind::AND, nm->mkNode(Kind::GEQ, t, d_zero), iZero),
                   nm->mkNode(Kind::AND, sZero, tNZ)),
        InferenceId::ARITH_NL_EXP_BOUND_CASE_REFINE,
        nullptr,
        true);
  }
  // bnd5, in the SAME generalized form addBoundingLemmas uses:
  //     s >= 2 /\ t >= 2  =>  exp(s,t) >= s*s*(t-1)
  // The paper's s+t > 4 /\ s > 1 /\ t > 1 => exp(s,t) > s*t+1 is never built
  // as a node anywhere in this solver -- the generalized bound is strictly
  // larger on the whole of the paper's region and additionally covers
  // s = t = 2, which the paper's guard excludes.
  //
  // This is the one whose conclusion is non-linear, and the reason the paper
  // puts bounding BELOW monotonicity in the precedence order -- so holding it
  // back until a model violates it is exactly the intent. The firing test
  // below is the model-side reading of the generalized conclusion.
  if (ms >= Integer(2) && mt >= Integer(2) && mv < ms * ms * (mt - one))
  {
    addExpLemma(
        nm->mkNode(Kind::IMPLIES,
                   nm->mkNode(Kind::AND,
                              nm->mkNode(Kind::GEQ, s, d_two),
                              nm->mkNode(Kind::GEQ, t, d_two)),
                   nm->mkNode(Kind::GEQ,
                              i,
                              nm->mkNode(Kind::MULT,
                                         nm->mkNode(Kind::MULT, s, s),
                                         nm->mkNode(Kind::SUB, t, d_one)))),
        InferenceId::ARITH_NL_EXP_BOUND_CASE_REFINE,
        nullptr,
        true);
  }
}

void ExpSolver::checkPrimeLemma(Node n,
                                const Integer& model_s,
                                const Integer& expx)
{
  // prime: divisible_d(s) /\ t != 0 => divisible_d(exp(s,t)) and
  // t > 0 /\ divisible_d(exp(s,t)) => divisible_d(s), for the
  // smallest prime d dividing exactly one of |M(s)| and |M(exp(s,t))|. Only
  // relevant when the model's prime factorizations disagree (M(s),M(exp)>=2).
  if (model_s < Integer(2) || expx < Integer(2)) return;
  Integer a = model_s.abs();
  Integer b = expx.abs();
  Integer d(0);
  const uint64_t cap = 100000;
  for (uint64_t p = 2; p <= cap; ++p)
  {
    bool isPrime = true;
    for (uint64_t k = 2; k * k <= p; ++k)
    {
      if (p % k == 0)
      {
        isPrime = false;
        break;
      }
    }
    if (!isPrime) continue;
    Integer P(p);
    bool da = a.euclidianDivideRemainder(P).isZero();
    bool db = b.euclidianDivideRemainder(P).isZero();
    if (da != db)
    {
      d = P;
      break;
    }
  }
  if (d.isZero()) return;  // no discriminating prime within the cap
  NodeManager* nm = nodeManager();
  Node s = n[0];
  Node t = n[1];
  Node dc = nm->mkConstInt(Rational(d));
  Node divExp = nm->mkNode(
      Kind::EQUAL, nm->mkNode(Kind::INTS_MODULUS, n, dc), d_zero);
  Node divS = nm->mkNode(
      Kind::EQUAL, nm->mkNode(Kind::INTS_MODULUS, s, dc), d_zero);
  Node tNZ = nm->mkNode(Kind::EQUAL, t, d_zero).notNode();
  // The converse only holds for t > 0: for t < 0, s^t = 0 is divisible by d
  // whatever s is.
  Node lem = nm->mkNode(
      Kind::IMPLIES, nm->mkNode(Kind::AND, divS, tNZ), divExp);
  addExpLemma(
      lem, InferenceId::ARITH_NL_EXP_INIT_REFINE, nullptr, true);
  Node tPos = nm->mkNode(Kind::GT, t, d_zero);
  Node conv = nm->mkNode(
      Kind::IMPLIES, nm->mkNode(Kind::AND, tPos, divExp), divS);
  addExpLemma(
      conv, InferenceId::ARITH_NL_EXP_INIT_REFINE, nullptr, true);
}

void ExpSolver::checkInductionLemma(Node n,
                                    Node m,
                                    const Integer& model_s,
                                    const Integer& model_t,
                                    const Integer& model_sy,
                                    const Integer& model_ty)
{
  // ind: s1=s2 /\ t2-d=t1>=0 => exp(s2,t2) = exp(s1,t1) * s1^d, where d>0 is
  // the model exponent gap between two same-base EXP terms.
  if (!(model_s == model_sy)) return;  // need a common base in the model
  Node big, small;
  Integer tSmall;
  if (model_t > model_ty)
  {
    big = n;
    small = m;
    tSmall = model_ty;
  }
  else if (model_ty > model_t)
  {
    big = m;
    small = n;
    tSmall = model_t;
  }
  else
  {
    return;  // equal exponents: nothing to unroll
  }
  if (tSmall.sgn() < 0) return;  // need t1 >= 0
  Integer d = (model_t - model_ty).abs();  // > 0
  if (d > Integer(256)) return;            // cap the s1^d product size
  uint32_t dd = d.toUnsignedInt();
  // Skip if the model already satisfies the identity.
  Node vBig = d_model.computeAbstractModelValue(big);
  Node vSmall = d_model.computeAbstractModelValue(small);
  if (vBig.isConst() && vSmall.isConst())
  {
    Integer eb = vBig.getConst<Rational>().getNumerator();
    Integer es = vSmall.getConst<Rational>().getNumerator();
    if (eb == es * model_s.pow(dd)) return;
  }
  NodeManager* nm = nodeManager();
  Node sBig = big[0], tBig = big[1];
  Node sSmall = small[0], tSmallT = small[1];
  Node sameBase = nm->mkNode(Kind::EQUAL, sSmall, sBig);
  Node dc = nm->mkConstInt(Rational(d));
  Node gap = nm->mkNode(
      Kind::EQUAL, nm->mkNode(Kind::SUB, tBig, dc), tSmallT);
  Node tsGeq0 = nm->mkNode(Kind::GEQ, tSmallT, d_zero);
  Node powNode;
  if (dd == 1)
  {
    powNode = sSmall;
  }
  else
  {
    std::vector<Node> copies(dd, sSmall);
    powNode = nm->mkNode(Kind::MULT, copies);
  }
  Node concl = nm->mkNode(
      Kind::EQUAL, big, nm->mkNode(Kind::MULT, small, powNode));
  Node lem = nm->mkNode(
      Kind::IMPLIES, nm->mkNode(Kind::AND, sameBase, gap, tsGeq0), concl);
  addExpLemma(
      lem, InferenceId::ARITH_NL_EXP_INDUCTION_REFINE, nullptr, true);
}

void ExpSolver::checkInterpolationLemma(Node n,
                                        const Integer& c,
                                        const Integer& d,
                                        const Integer& expx)
{
  // Bilinear-interpolation bounds (Thm. 4.17): a convex function lies below
  // its secant inside an interval and above it outside. We emit an upper
  // bound (ip2) when M(exp) > c^d and a lower bound (ip3) when M(exp) < c^d.
  // Handled elsewhere: c<=0 or d<=0 (symmetry / bnd1).
  const Integer one(1);
  const uint32_t kExpCap = 32;  // bound c^d constant blow-up
  if (c < one || d < one) return;
  if (!d.fitsUnsignedInt() || d > Integer(kExpCap)) return;
  Integer cd = c.pow(d.toUnsignedInt());
  if (expx == cd) return;  // this term is not actually violated
  NodeManager* nm = nodeManager();
  Node s = n[0];
  Node t = n[1];

  // Build (scale, rhs) with rhs = scale * ip^{[cLo,cHi][dLo,dHi]}(s,t), an
  // integer-coefficient bilinear term (denominators cleared). Returns false
  // if an exponent is out of range. Uses the convention a/0 := 0, which here
  // is automatic since cLo==cHi forces the slope numerators to 0.
  auto buildRhs = [&](const Integer& cLo,
                      const Integer& cHi,
                      const Integer& dLo,
                      const Integer& dHi,
                      Node& rhsOut,
                      Integer& scaleOut) -> bool {
    if (!dLo.fitsUnsignedInt() || !dHi.fitsUnsignedInt()) return false;
    if (dHi > Integer(kExpCap)) return false;
    Integer P = cHi - cLo, Q = dHi - dLo;
    Integer Pm = P.isZero() ? one : P;
    Integer Qm = Q.isZero() ? one : Q;
    uint32_t eLo = dLo.toUnsignedInt(), eHi = dHi.toUnsignedInt();
    Integer cm_dl = cLo.pow(eLo), cm_dh = cLo.pow(eHi);
    Integer cp_dl = cHi.pow(eLo), cp_dh = cHi.pow(eHi);
    Integer slopeA = cp_dl - cm_dl;  // (c+)^d- - (c-)^d-, later /P
    Integer slopeB = cp_dh - cm_dh;  // (c+)^d+ - (c-)^d+, later /P
    Node xmc = nm->mkNode(Kind::SUB, s, nm->mkConstInt(Rational(cLo)));
    Node AP = nm->mkNode(
        Kind::ADD,
        nm->mkConstInt(Rational(cm_dl * Pm)),
        nm->mkNode(Kind::MULT, nm->mkConstInt(Rational(slopeA)), xmc));
    Node BP = nm->mkNode(
        Kind::ADD,
        nm->mkConstInt(Rational(cm_dh * Pm)),
        nm->mkNode(Kind::MULT, nm->mkConstInt(Rational(slopeB)), xmc));
    Node ymd = nm->mkNode(Kind::SUB, t, nm->mkConstInt(Rational(dLo)));
    rhsOut = nm->mkNode(
        Kind::ADD,
        nm->mkNode(Kind::MULT, AP, nm->mkConstInt(Rational(Qm))),
        nm->mkNode(Kind::MULT, nm->mkNode(Kind::SUB, BP, AP), ymd));
    scaleOut = Pm * Qm;
    return true;
  };

  if (expx > cd)
  {
    // ip2 upper bound: use the stored point nearest to (c,d) as the secant's
    // second point, defaulting to (c,d) itself (a single-point/tight lemma).
    Integer cp = c, dp = d, best(-1);
    for (const auto& pt : d_interpPoints)
    {
      Integer dist = (pt.first - c).abs() + (pt.second - d).abs();
      if (best.sgn() < 0 || dist < best)
      {
        best = dist;
        cp = pt.first;
        dp = pt.second;
      }
    }
    Integer cLo = c < cp ? c : cp, cHi = c < cp ? cp : c;
    Integer dLo = d < dp ? d : dp, dHi = d < dp ? dp : d;
    Node rhs;
    Integer scale;
    if (buildRhs(cLo, cHi, dLo, dHi, rhs, scale))
    {
      Node guard = nm->mkNode(
          Kind::AND,
          {nm->mkNode(Kind::GEQ, s, nm->mkConstInt(Rational(cLo))),
           nm->mkNode(Kind::LEQ, s, nm->mkConstInt(Rational(cHi))),
           nm->mkNode(Kind::GEQ, t, nm->mkConstInt(Rational(dLo))),
           nm->mkNode(Kind::LEQ, t, nm->mkConstInt(Rational(dHi)))});
      Node lhs = nm->mkNode(Kind::MULT, nm->mkConstInt(Rational(scale)), n);
      Node lem = nm->mkNode(
          Kind::IMPLIES, guard, nm->mkNode(Kind::LEQ, lhs, rhs));
      addExpLemma(
          lem, InferenceId::ARITH_NL_EXP_BOUND_CASE_REFINE, nullptr, true);
    }
    d_interpPoints.emplace_back(c, d);
  }
  else
  {
    // ip3 lower bound over the adjacent unit square [c,c+1] x [d,d+1]; here
    // all denominators are 1, so no scaling is needed. Valid for s>=1, t>=d.
    Node rhs;
    Integer scale;
    if (buildRhs(c, c + one, d, d + one, rhs, scale))
    {
      Node guard = nm->mkNode(
          Kind::AND,
          nm->mkNode(Kind::GEQ, s, d_one),
          nm->mkNode(Kind::GEQ, t, nm->mkConstInt(Rational(d))));
      Node lhs = nm->mkNode(Kind::MULT, nm->mkConstInt(Rational(scale)), n);
      Node lem = nm->mkNode(
          Kind::IMPLIES, guard, nm->mkNode(Kind::GEQ, lhs, rhs));
      addExpLemma(
          lem, InferenceId::ARITH_NL_EXP_BOUND_CASE_REFINE, nullptr, true);
    }
  }
}


//---------------------------------------------------------------------------
// SwInE phasing (Frohn & Giesl Sect. 5 / Alg. 3).
//---------------------------------------------------------------------------

bool ExpSolver::emitPhaseSplit(Node i)
{
  Assert(i.getKind() == Kind::EXP);
  NodeManager* nm = nodeManager();
  std::pair<Node, uint64_t> key(i, d_phaseB);
  auto it = d_phaseGuards.find(key);
  if (it == d_phaseGuards.end())
  {
    std::stringstream ss;
    ss << "__exp_phase_" << d_phaseB;
    it = d_phaseGuards
             .emplace(key,
                      NodeManager::mkDummySkolem(
                          ss.str(),
                          nm->booleanType(),
                          "phasing guard for --arith-exp-phasing"))
             .first;
  }
  Node guard = it->second;
  if (d_phaseEmitted.contains(guard))
  {
    // already split this term at this level
    return false;
  }
  d_phaseEmitted.insert(guard);

  Node t = i[1];
  Node lb = nm->mkNode(Kind::GEQ, t, nm->mkConstInt(Rational(-d_phaseBound)));
  Node ub = nm->mkNode(Kind::LEQ, t, nm->mkConstInt(Rational(d_phaseBound)));
  Node lem = guard.eqNode(nm->mkNode(Kind::AND, lb, ub));
  Trace("exp-lemma") << "ExpSolver::Lemma: " << lem << " ; PHASE_SPLIT(b = "
                     << d_phaseB << ")" << std::endl;
  // Sent directly, NOT through addExpLemma: this is the definition of a
  // fresh guard Boolean (search control), not a theorem about EXP, so
  // --check-lemmas must neither record nor try to validate it.
  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_EXP_PHASE_BOUND);
  // Steer the search into the bounded region, i.e. into the sat-phase. The
  // guard alone would do, but preferring the bound atoms as well means the
  // phase survives the solver deciding one of them first.
  preferAtom(guard, true);
  preferAtom(lb, true);
  preferAtom(ub, true);
  return true;
}

bool ExpSolver::checkPhase()
{
  // Alg. 3 lines 9/11: is this candidate model a model of the sat-phase query,
  // i.e. does it respect the level-b bound on every relevant exponent?
  bool inBound = true;
  for (const Node& n : d_exps)
  {
    Node vt = d_model.computeConcreteModelValue(n[1]);
    if (!vt.isConst())
    {
      continue;
    }
    if (vt.getConst<Rational>().getNumerator().abs() > d_phaseBound)
    {
      inBound = false;
      break;
    }
  }
  if (inBound)
  {
    // Sat-phase counterexample: refine as usual (Alg. 3 lines 17-23).
    return false;
  }
  // Unsat-phase counterexample (Alg. 3 lines 13-15): raise the bound and go
  // back to the sat-phase. Alg. 3 discards the model here without calling
  // ComputeLemmas -- precisely to avoid deriving interpolation lemmas from the
  // large exponents that make the backend stall -- so we tell the caller to
  // skip refinement for this round. The new splits are what invalidates the
  // candidate model, so only skip when one was actually emitted.
  d_phaseB++;
  d_phaseBound = d_phaseBound * Integer(2);
  Trace("exp") << "ExpSolver: phasing raises b to " << d_phaseB
               << " (exponent bound " << d_phaseBound << ")" << std::endl;
  bool emitted = false;
  for (const Node& e : d_exps)
  {
    emitted |= emitPhaseSplit(e);
  }
  return emitted;
}

void ExpSolver::preferAtom(Node atom, bool pol)
{
  Node a = rewrite(atom);
  if (a.getKind() == Kind::NOT)
  {
    a = a[0];
    pol = !pol;
  }
  if (a.isConst())
  {
    // trivially (un)satisfied after rewriting, nothing to decide
    return;
  }
  Node lit = d_astate.getValuation().ensureLiteral(a);
  if (lit.isNull())
  {
    return;
  }
  if (lit.getKind() == Kind::NOT)
  {
    lit = lit[0];
    pol = !pol;
  }
  d_im.preferPhase(lit, pol);
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

