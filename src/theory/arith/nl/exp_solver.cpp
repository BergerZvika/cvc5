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
      d_initRefine(userContext())
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
    Node s = i[0];
    Node t = i[1];

    // Phasing (Alg. 3 line 9): put this term's exponent under the level-b
    // bound, so the sat-phase is entered before the first full-refinement
    // round rather than after it.
    if (options().arith.expPhasing)
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

    // even:  s mod 2 = 0 /\ t >= 1  =>  exp(s, t) mod 2 = 0
    Node smod2 = nm->mkNode(Kind::INTS_MODULUS, s, d_two);
    Node imod2 = nm->mkNode(Kind::INTS_MODULUS, i, d_two);
    Node sEven = nm->mkNode(Kind::EQUAL, smod2, d_zero);
    Node tgeq1 = nm->mkNode(Kind::GEQ,  t, d_one);
    Node iEven = nm->mkNode(Kind::EQUAL, imod2, d_zero);
    conj.push_back(nm->mkNode(Kind::IMPLIES,
                                nm->mkNode(Kind::AND, sEven, tgeq1),
                                iEven));
    
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
    
    // neg -1: s = -1 /\ t < 0 =>  exp(s, t) = exp(s,-t)
    Node tlt0 = nm->mkNode(Kind::LT, t, d_zero);
    Node seqm1  = nm->mkNode(Kind::EQUAL, s, d_negone);
    Node negT   = nm->mkNode(Kind::NEG, t);
    Node mirror = nm->mkNode(Kind::EXP, s, negT);
    conj.push_back(nm->mkNode(Kind::IMPLIES,
                                nm->mkNode(Kind::AND, seqm1, tlt0),
                                i.eqNode(mirror)));
    
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
      Node recip = nm->mkNode(Kind::INTS_DIVISION, d_one, mirror);
      conj.push_back(nm->mkNode(Kind::IMPLIES, tlt0, i.eqNode(recip)));
    }

    // SwInE static lemma families (Frohn & Giesl), gated by
    // --arith-exp-lemmas. Symmetry and bounding need no model, so they are
    // emitted here as initial-refine axioms.
    {
      // Static (non-model) families emitted as initial-refine axioms. Symmetry
      // is NOT here; it is emitted only in the full-refine loop (see
      // checkSymmetryRefine).
      ExpFeatureSet lsel(options().arith.expLemmasMode);
      // --arith-exp-bounding=refine moves these into the refinement loop, where
      // they are filtered by what the candidate model actually violates.
      if (lsel.has("bounding")
          && options().arith.expBoundingMode
                 != options::ExpBoundingMode::REFINE)
      {
        addBoundingLemmas(i, conj);
      }
    }

    Node lem = nm->mkAnd(conj);
    Trace("exp-lemma") << "ExpSolver::Lemma: " << lem << " ; INIT_REFINE"
                        << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_EXP_INIT_REFINE);
  }
}


// void ExpSolver::sortExpsBasedOnModel() {}

void ExpSolver::checkFullRefine() {
    Trace("exp-check") << "ExpSolver::checkFullRefine" << std::endl;
  NodeManager* nm = nodeManager();
  // Phasing (Alg. 3 lines 11-15): an unsat-phase counterexample is discarded
  // without computing any refinement lemmas -- raising the bound and going
  // back to the sat-phase is the whole of the round.
  if (options().arith.expPhasing && checkPhase())
  {
    return;
  }
  // SwInE model-based lemma families gated by --arith-exp-lemmas.
  ExpFeatureSet lsel(options().arith.expLemmasMode);
  bool primeOn = lsel.has("prime");
  bool indOn = lsel.has("induction");
  bool interpOn = lsel.has("interpolation");
  // The 'symmetry' mode -- and the aggregate 'all-lemmas'/'all' -- emit the
  // symmetry lemmas here (in the full-refinement loop), for model-violating
  // terms.
  bool symRefineOn = lsel.has("symmetry");
  // The 'compose' mode emits the composition lemma in the full-refinement loop
  // for model-violating nested EXP terms.
  bool composeOn = lsel.has("compose");
  // General monotonicity (Frohn & Giesl `mon`). It subsumes the two same-base
  // pair lemmas below, so those are suppressed while it is on, and it runs as
  // its own scan over ALL pairs -- the loop below only ever reaches a pair
  // whose first element is itself model-violating, which would hide exactly
  // the cross-base cases `mon` exists for.
  bool genMon = options().arith.expMonGeneral;
  if (genMon)
  {
    checkMonotonicityRefine();
  }
  // Guarded same-base fusion. Like monotonicity this is its own scan over ALL
  // pairs rather than a step inside the violating-term loop below: the pair
  // that closes the goal need not have a violating term as its first element.
  if (lsel.has("fuse"))
  {
    checkFuseRefine();
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

    // add monotinicity lemmas
    for (uint64_t j = i + 1; j < size; j++)
    {
      Node m = d_exps[j];
      Node sy = m[0];
      Node ty = m[1];
      Node valSY = d_model.computeConcreteModelValue(sy);
      Node valTY = d_model.computeConcreteModelValue(ty);

      Integer model_sy = valSY.getConst<Rational>().getNumerator();
      Integer model_ty = valTY.getConst<Rational>().getNumerator();
      // Abstract model value of m = exp(s_y, t_y). This must be m's own value
      // (not n's): the guards below only emit a pairwise lemma when BOTH
      // instances' model values together violate it. (Previously this read
      // valExpxAbstract, i.e. expx, so every such guard was trivially true and
      // the lemmas fired even when the model already satisfied them.)
      Node valExpyAbstract = d_model.computeAbstractModelValue(m);
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
        d_im.addPendingLemma(
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
        d_im.addPendingLemma(
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
          d_im.addPendingLemma(
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
          d_im.addPendingLemma(
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
          d_im.addPendingLemma(
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
    if (lsel.has("bounding")
        && options().arith.expBoundingMode != options::ExpBoundingMode::INIT)
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
      d_im.addPendingLemma(lem,
                           InferenceId::ARITH_NL_EXP_BOUND_CASE_REFINE,
                           nullptr,
                           true);
    }



    // neg reciprocal:  t < 0  =>  exp(s, t) = 1 div exp(s, -t)
    // Only sound under integer div when t < 0 (both sides collapse to 0/1);
    // for t >= 0 it would force exp(s,t) = 1 div 0 = 0, so it is guarded here.
    // Emitted only when --arith-exp-neg-recip=refine (default off; the 'init'
    // mode emits it once per term from checkInitialRefine instead).
    if (options().arith.expNegRecipMode == options::ExpNegRecipMode::REFINE)
    {
      Node tlt0 = nm->mkNode(Kind::LT, t, d_zero);
      Node negT = nm->mkNode(Kind::NEG, t);
      Node mirror = nm->mkNode(Kind::EXP, s, negT);
      Node recip = nm->mkNode(Kind::INTS_DIVISION, d_one, mirror);
      Node negRecipLem = nm->mkNode(Kind::IMPLIES, tlt0, n.eqNode(recip));
      d_im.addPendingLemma(negRecipLem,
                           InferenceId::ARITH_NL_EXP_INIT_REFINE,
                           nullptr,
                           true);
    }

    // this is the most naive model-based schema based on model values
    Node lem = valueBasedLemma(n);
    Trace("pow2-lemma") << "Pow2Solver::Lemma: " << lem << " ; VALUE_REFINE"
                        << std::endl;
    // send the value lemma
    d_im.addPendingLemma(
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
      d_im.addPendingLemma(
          lem, InferenceId::ARITH_NL_EXP_MONOTONE_REFINE, nullptr, true);
    }
  }
}

void ExpSolver::checkFuseRefine()
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

  for (size_t i = 0, size = pts.size(); i < size; i++)
  {
    for (size_t j = i + 1; j < size; j++)
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
      d_im.addPendingLemma(
          lem, InferenceId::ARITH_NL_EXP_FUSE_REFINE, nullptr, true);
    }
  }
}

void ExpSolver::checkComposeRefine(Node n)
{
  // Exponent-composition lemma (EIA-valid) for a model-violating nested term
  // n (n is already known wrong here): exp(exp(x,y),z) = exp(x, y*z).
  if (n[0].getKind() != Kind::EXP) return;
  NodeManager* nm = nodeManager();
  Node yz = nm->mkNode(Kind::MULT, n[0][1], n[1]);
  Node lem = n.eqNode(nm->mkNode(Kind::EXP, n[0][0], yz));
  d_im.addPendingLemma(
      lem, InferenceId::ARITH_NL_EXP_INIT_REFINE, nullptr, true);
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
  Node expNegT = nm->mkNode(Kind::EXP, s, nm->mkNode(Kind::NEG, t));
  Node tEvenPred = nm->mkNode(
      Kind::EQUAL, nm->mkNode(Kind::INTS_MODULUS, t, d_two), d_zero);
  bool tEven = model_t.euclidianDivideRemainder(Integer(2)).isZero();
  if (tEven)
  {
    // sym1: divisible2(t) => exp(s,t) = exp(-s,t)
    d_im.addPendingLemma(
        nm->mkNode(Kind::IMPLIES, tEvenPred, n.eqNode(expNegS)),
        InferenceId::ARITH_NL_EXP_INIT_REFINE, nullptr, true);
  }
  else
  {
    // sym2: ~divisible2(t) => exp(s,t) = -exp(-s,t)
    d_im.addPendingLemma(
        nm->mkNode(Kind::IMPLIES,
                   tEvenPred.notNode(),
                   n.eqNode(nm->mkNode(Kind::NEG, expNegS))),
        InferenceId::ARITH_NL_EXP_INIT_REFINE, nullptr, true);
  }
  // sym3: exp(s,t) = exp(s,-t) (unconditional; n is a model-violating term).
  d_im.addPendingLemma(n.eqNode(expNegT),
                       InferenceId::ARITH_NL_EXP_INIT_REFINE, nullptr, true);
}

void ExpSolver::addBoundingLemmas(Node i, std::vector<Node>& conj)
{
  // bnd2: t=1               => exp(s,t) = s
  // bnd3: s=0 /\ t!=0      <=> exp(s,t) = 0
  // bnd5: s>=2 /\ t>=2      => exp(s,t) >= s*s*(t-1)   (generalized; see below)
  // (bnd1 t=0=>exp=1 and bnd4 s=1=>exp=1 are already emitted unconditionally.)
  NodeManager* nm = nodeManager();
  Node s = i[0];
  Node t = i[1];
  conj.push_back(nm->mkNode(
      Kind::IMPLIES, nm->mkNode(Kind::EQUAL, t, d_one), i.eqNode(s)));
  Node sZero = nm->mkNode(Kind::EQUAL, s, d_zero);
  Node tNZ = nm->mkNode(Kind::EQUAL, t, d_zero).notNode();
  conj.push_back(nm->mkNode(Kind::EQUAL,
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
    d_im.addPendingLemma(nm->mkNode(Kind::IMPLIES,
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
    d_im.addPendingLemma(
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
    d_im.addPendingLemma(
        nm->mkNode(Kind::IMPLIES,
                   nm->mkNode(
                       Kind::AND, nm->mkNode(Kind::GEQ, t, d_zero), iZero),
                   nm->mkNode(Kind::AND, sZero, tNZ)),
        InferenceId::ARITH_NL_EXP_BOUND_CASE_REFINE,
        nullptr,
        true);
  }
  // bnd5: s+t > 4 /\ s > 1 /\ t > 1 => exp(s,t) > s*t+1. This is the one whose
  // conclusion is non-linear, and the reason the paper puts bounding BELOW
  // monotonicity in the precedence order -- so holding it back until a model
  // violates it is exactly the intent.
  if (ms >= Integer(2) && mt >= Integer(2) && mv < ms * ms * (mt - one))
  {
    d_im.addPendingLemma(
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
  // prime: divisible_d(exp(s,t)) <=> divisible_d(s) /\ t != 0, for the
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
  Node lem = nm->mkNode(
      Kind::EQUAL, divExp, nm->mkNode(Kind::AND, divS, tNZ));
  d_im.addPendingLemma(
      lem, InferenceId::ARITH_NL_EXP_INIT_REFINE, nullptr, true);
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
  d_im.addPendingLemma(
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
      d_im.addPendingLemma(
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
      d_im.addPendingLemma(
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

