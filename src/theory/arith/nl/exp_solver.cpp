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
#include "theory/arith/arith_msum.h"
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

ExpSolver::ExpSolver(Env& env, InferenceManager& im, NlModel& model)
    : EnvObj(env), d_im(im), d_model(model), d_initRefine(userContext())
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
      Integer expy = valExpxAbstract.getConst<Rational>().getNumerator();

      // monotonicity: 0 <= s_x /\ s_x = s_y /\ 0 <= t_x /\ t_x < t_y => exp(s_x, t_x) < exp(s_y,t_y)
      if (model_s >= 0  && model_t >= 0 && model_s == model_sy && model_t < model_ty && expy <= expx)
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
      else if (model_s >= 0 && model_ty >= 0 && model_s == model_sy && model_t > model_ty && expy >= expx)
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
      if (options().arith.nlExtExpInductionAxioms) {
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
        if (model_s >= 2 && model_ty >= 0 && model_s == model_sy && model_t > model_ty && expx < expy * model_ty) {
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

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
