/******************************************************************************
 * Top contributors (to current version):
 *    Zvika Berger
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of parametric integer and (PIAND) solver.
 */

#include "theory/arith/nl/piand_solver.h"

#include "options/arith_options.h"
#include "options/smt_options.h"
#include "preprocessing/passes/bv_to_int.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_state.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"
#include "expr/skolem_manager.h"
#include<cmath>

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

PIAndSolver::PIAndSolver(Env& env,
                       InferenceManager& im,
                       ArithState& state,
                       NlModel& model)
    : EnvObj(env),
      d_im(im),
      d_model(model),
      d_astate(state),
      d_initRefine(userContext())
{
  NodeManager* nm = NodeManager::currentNM();
  d_false = nm->mkConst(false);
  d_true = nm->mkConst(true);
  d_zero = nm->mkConstInt(Rational(0));
  d_one = nm->mkConstInt(Rational(1));
  d_two = nm->mkConstInt(Rational(2));
}

PIAndSolver::~PIAndSolver() {}

void PIAndSolver::initLastCall(const std::vector<Node>& assertions,
                              const std::vector<Node>& false_asserts,
                              const std::vector<Node>& xts)
{
  d_piands.clear();

  Trace("piand-mv") << "PIAND terms : " << std::endl;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    if (ak != PIAND)
    {
      // don't care about other terms
      continue;
    }
    d_piands[a[0]].push_back(a);
  }
  Trace("piand") << "We have " << d_piands.size() << " PIAND bit-width." << std::endl;
}

void PIAndSolver::checkInitialRefine()
{
  // std::cout << "init" << std::endl;
  Trace("piand-check") << "PIAndSolver::checkInitialRefine" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  // int j;
  int index;
  int skolem_num = 0;
  for (const std::pair<Node, std::vector<Node> >& is : d_piands)
  {
    index = -1;
    // the reference bitwidth
    Node k = is.first;
    for (const Node& i : is.second)
    {
      index++;
      Node x = i[1];
      Node y = i[2];
      if (d_initRefine.find(i) != d_initRefine.end())
      {
        // already sent initial axioms for i in this user context
        continue;
      }
      d_initRefine.insert(i);
      Node twok = nm->mkNode(kind::POW2, k);
      Node arg0Mod = nm->mkNode(kind::INTS_MODULUS, x, twok);
      Node arg1Mod = nm->mkNode(kind::INTS_MODULUS, y, twok);
      Node arg0Mod2 = nm->mkNode(kind::INTS_MODULUS, x, d_two);
      Node arg1Mod2 = nm->mkNode(kind::INTS_MODULUS, y, d_two);
      Node plus = nm->mkNode(kind::ADD , x, y);
      Node twok_minus_one = nm->mkNode(kind::SUB, twok, d_one);
      Node k_gt_0 = nm->mkNode(kind::GT, k, d_zero);
      Node x_geq_zero = nm->mkNode(kind::GEQ, x, d_zero);
      Node x_lt_pow2 = nm->mkNode(LT, x, twok);
      Node x_range = nm->mkNode(AND, x_geq_zero, x_lt_pow2);
      Node y_geq_zero = nm->mkNode(kind::GEQ, y, d_zero);
      Node y_lt_pow2 = nm->mkNode(LT, y, twok);
      Node y_range = nm->mkNode(AND, y_geq_zero, y_lt_pow2);
      // initial refinement lemmas
      std::vector<Node> conj;
      Assert(x <= y);
      if (options().smt.PiandMode == options::PIandMode::PIAND) {
        // max: x > 0 && y = 2^k -1 -> piand(k,x,y) = x mod 2^k
        Node y_modpow2_eq_max = nm->mkNode(kind::EQUAL, y, twok_minus_one);
        Node assum_max = nm->mkNode(AND, k_gt_0, y_modpow2_eq_max, x_range);
        conj.push_back(nm->mkNode(IMPLIES, assum_max, i.eqNode(x)));
        // max: y > 0 && x = 2^k -1 -> piand(k,x,y) = y mod 2^k
        Node x_modpow2_eq_max = nm->mkNode(kind::EQUAL, x, twok_minus_one);
        Node assum_max_x = nm->mkNode(AND, k_gt_0, x_modpow2_eq_max, y_range);
        conj.push_back(nm->mkNode(IMPLIES, assum_max_x, i.eqNode(y)));
        // min: y = 0 -> piand(k,x,y) = 0
        Node eq_y_zero = nm->mkNode(kind::EQUAL, y, d_zero);
        conj.push_back(nm->mkNode(kind::IMPLIES, eq_y_zero,  i.eqNode(d_zero)));
        // min-x: x = 0 -> piand(k,x,y) = 0
        Node eq_x_zero = nm->mkNode(kind::EQUAL, x, d_zero);
        conj.push_back(nm->mkNode(kind::IMPLIES, eq_x_zero,  i.eqNode(d_zero)));
        // idempotence: k > 0 && x mod 2^k  = y mod 2^k  ->  piand(k,x,y) = x mod 2^k
        Node eq_y_x = nm->mkNode(kind::EQUAL, y, x);
        Node assum_idempotence= nm->mkNode(AND, k_gt_0, eq_y_x, x_range);
        conj.push_back(nm->mkNode(kind::IMPLIES, assum_idempotence,  i.eqNode(x)));
        // symmetry: piand(k, x,y) = piand(k, y,x)
        Node piand_y_x = nm->mkNode(kind::PIAND, k, y, x);
        conj.push_back(nm->mkNode(kind::EQUAL, i,  piand_y_x));
        // range1: 0 <= piand(x,y)
        conj.push_back(nm->mkNode(LEQ, d_zero, i));
        // range 2: piand(x,y)<=mod(x, 2^k)
        Node i_leq_x = nm->mkNode(LEQ, i, x);
        conj.push_back(nm->mkNode(IMPLIES, x_geq_zero, i_leq_x));
        // range 3: piand(x,y)<=mod(y, 2^k)
        Node i_leq_y = nm->mkNode(LEQ, i, y);
        conj.push_back(nm->mkNode(IMPLIES, y_geq_zero, i_leq_y));
        // negative bitwidth: k <= 0 -> piand(k, x, y) = 0
        Node k_le_0 = nm->mkNode(kind::LEQ, k, d_zero);
        conj.push_back(nm->mkNode(IMPLIES, k_le_0, i.eqNode(d_zero)));
        // even lemmas: x % 2 = 0 => piand(k,x,y) % 2 = 0
        Node piand_mod_two = nm->mkNode(kind::INTS_MODULUS, i, d_two);
        Node arg1Mod2_eq_zero = nm->mkNode(kind::EQUAL, arg1Mod2, d_zero);
        conj.push_back(nm->mkNode(IMPLIES, arg1Mod2_eq_zero, piand_mod_two.eqNode(d_zero)));
        // even lemmas: y % 2 = 0 => piand(k,x,y) % 2 = 0
        Node arg0Mod2_eq_zero = nm->mkNode(kind::EQUAL, arg0Mod2, d_zero);
        conj.push_back(nm->mkNode(IMPLIES, arg0Mod2_eq_zero, piand_mod_two.eqNode(d_zero)));
        
        // insert lemmas
        Node lem = conj.size() == 1 ? conj[0] : nm->mkNode(AND, conj);
        Trace("piand-lemma") << "PIAndSolver::Lemma: " << lem << " ; INIT_REFINE"
                            << std::endl;
        d_im.addPendingLemma(lem, InferenceId::ARITH_NL_PIAND_INIT_REFINE);

      } else if (options().smt.PiandMode == options::PIandMode::PIAND_OPT) {
        // max: x > 0 && y mod x^k = 2^k -1 -> piand(k,x,y) = x mod 2^k
        Node y_modpow2_eq_max = nm->mkNode(kind::EQUAL, y, twok_minus_one);
        // Node assum_max = nm->mkNode(AND, k_gt_0, y_modpow2_eq_max, x_range);
        conj.push_back(nm->mkNode(IMPLIES, y_modpow2_eq_max, i.eqNode(x)));
        // min: y mod 2^k = 0 -> piand(k,x,y) = 0
        Node eq_y_zero = nm->mkNode(kind::EQUAL, y, d_zero);
        conj.push_back(nm->mkNode(kind::IMPLIES, eq_y_zero,  i.eqNode(d_zero)));
        // min: y mod 2^k = 0 -> piand(k,x,y) = 0
        Node eq_x_zero = nm->mkNode(kind::EQUAL, x, d_zero);
        conj.push_back(nm->mkNode(kind::IMPLIES, eq_x_zero,  i.eqNode(d_zero)));
        // idempotence: k > 0 && x mod 2^k  = y mod 2^k  ->  piand(k,x,y) = x mod 2^k
        Node eq_y_x = nm->mkNode(kind::EQUAL, y, x);
        // Node assum_idempotence= nm->mkNode(AND, k_gt_0, eq_y_x, x_range);
        conj.push_back(nm->mkNode(kind::IMPLIES, eq_y_x,  i.eqNode(x)));
        // symmetry: piand(k, x,y) = piand(k, y,x)
        Node piand_y_x = nm->mkNode(kind::PIAND, k, y, x);
        conj.push_back(nm->mkNode(kind::EQUAL, i,  piand_y_x));
        // range1: 0 <= piand(x,y)
        conj.push_back(nm->mkNode(LEQ, d_zero, i));
        // range 2: piand(x,y)<=mod(x, 2^k)
        conj.push_back(nm->mkNode(LEQ, i, x));
        // range 3: piand(x,y)<=mod(y, 2^k)
        conj.push_back(nm->mkNode(LEQ, i, y));
        // negative bitwidth: k <= 0 -> piand(k, x, y) = 0
        Node k_le_0 = nm->mkNode(kind::LEQ, k, d_zero);
        conj.push_back(nm->mkNode(IMPLIES, k_le_0, i.eqNode(d_zero)));
        // even lemmas: x % 2 = 0 => piand(k,x,y) % 2 = 0
        Node piand_mod_two = nm->mkNode(kind::INTS_MODULUS, i, d_two);
        Node arg1Mod2_eq_zero = nm->mkNode(kind::EQUAL, arg1Mod2, d_zero);
        conj.push_back(nm->mkNode(IMPLIES, arg1Mod2_eq_zero, piand_mod_two.eqNode(d_zero)));
        // even lemmas: y % 2 = 0 => piand(k,x,y) % 2 = 0
        Node arg0Mod2_eq_zero = nm->mkNode(kind::EQUAL, arg0Mod2, d_zero);
        conj.push_back(nm->mkNode(IMPLIES, arg0Mod2_eq_zero, piand_mod_two.eqNode(d_zero)));
        
        // insert lemmas
        Node lem = conj.size() == 1 ? conj[0] : nm->mkNode(AND, conj);
        Trace("piand-lemma") << "PIAndSolver::Lemma: " << lem << " ; INIT_REFINE"
                            << std::endl;
        d_im.addPendingLemma(lem, InferenceId::ARITH_NL_PIAND_INIT_REFINE);

      } else if (options().smt.PiandMode == options::PIandMode::NO_CEGAR) {
        // max: x > 0 && y mod x^k = 2^k -1 -> piand(k,x,y) = x mod 2^k
        Node y_modpow2_eq_max = nm->mkNode(kind::EQUAL, arg1Mod, twok_minus_one);
        Node assum_max = nm->mkNode(AND, k_gt_0, y_modpow2_eq_max);
        conj.push_back(nm->mkNode(IMPLIES, assum_max, i.eqNode(arg0Mod)));
        // min: y mod 2^k = 0 -> piand(k,x,y) = 0
        Node eq_y_zero = nm->mkNode(kind::EQUAL, arg1Mod, d_zero);
        conj.push_back(nm->mkNode(kind::IMPLIES, eq_y_zero,  i.eqNode(d_zero)));
        // idempotence: k > 0 && x mod 2^k  = y mod 2^k  ->  piand(k,x,y) = x mod 2^k
        Node eq_y_x = nm->mkNode(kind::EQUAL, arg1Mod, arg0Mod);
        Node assum_idempotence= nm->mkNode(AND, k_gt_0, eq_y_x);
        conj.push_back(nm->mkNode(kind::IMPLIES, assum_idempotence,  i.eqNode(arg0Mod)));
        // symmetry: piand(k, x,y) = piand(k, y,x)
        Node piand_y_x = nm->mkNode(kind::PIAND, k, y, x);
        conj.push_back(nm->mkNode(kind::EQUAL, i,  piand_y_x));
        // range1: 0 <= piand(x,y)
        conj.push_back(nm->mkNode(LEQ, d_zero, i));
        // range 2: piand(x,y)<=mod(x, 2^k)
        conj.push_back(nm->mkNode(LEQ, i, arg0Mod));
        // range 3: piand(x,y)<=mod(y, 2^k)
        conj.push_back(nm->mkNode(LEQ, i, arg1Mod));
        // negative bitwidth: k <= 0 -> piand(k, x, y) = 0
        Node k_le_0 = nm->mkNode(kind::LEQ, k, d_zero);
        conj.push_back(nm->mkNode(IMPLIES, k_le_0, i.eqNode(d_zero)));
        // even lemmas: x % 2 = 0 => piand(k,x,y) % 2 = 0
        Node piand_mod_two = nm->mkNode(kind::INTS_MODULUS, i, d_two);
        Node arg0Mod2_eq_zero = nm->mkNode(kind::EQUAL, arg0Mod2, d_zero);
        conj.push_back(nm->mkNode(IMPLIES, arg0Mod2_eq_zero, piand_mod_two.eqNode(d_zero)));
        // even lemmas: y % 2 = 0 => piand(k,x,y) % 2 = 0
        Node arg1Mod2_eq_zero = nm->mkNode(kind::EQUAL, arg1Mod2, d_zero);
        conj.push_back(nm->mkNode(IMPLIES, arg1Mod2_eq_zero, piand_mod_two.eqNode(d_zero)));
        
        // x+y = 2^k-1 => piand(x,y) = 0
        Node plus_xy = nm->mkNode(kind::ADD , arg0Mod, arg1Mod);
        conj.push_back(nm->mkNode(IMPLIES, plus_xy.eqNode(twok_minus_one), i.eqNode(d_zero)));
        // piand(1,x,y) = min(ex0(x), ex0(y))
        Node k_eq_one = nm->mkNode(kind::EQUAL, k, d_one);
        Node arg0Mod2_big = nm->mkNode(kind::GEQ, arg0Mod2, arg1Mod2);
        Node min_ex0 = nm->mkNode(kind::ITE, arg0Mod2_big, arg0Mod2, arg1Mod2);
        conj.push_back(nm->mkNode(kind::IMPLIES, k_eq_one,  min_ex0));
        // difference: x != x2 /\ y = y2 => piand(x,y) != x2 \/ piand(x2, y2) != x 
        int j = -1;
        for (const Node& n : is.second)
        {
          j++;
          if(j > index) {
            Node x2 = n[1];
            Node y2 = n[2];
            Node power2_k = nm->mkNode(kind::POW2, k);
            Node arg20Mod = nm->mkNode(kind::INTS_MODULUS, x2, power2_k);
            Node arg21Mod = nm->mkNode(kind::INTS_MODULUS, y2, power2_k);
            Node noneqx = nm->mkNode(AND, (arg0Mod.eqNode(arg20Mod)).notNode(), arg1Mod.eqNode(arg21Mod));
            Node difference = nm->mkNode(OR, i.eqNode(arg20Mod).notNode(), n.eqNode(arg0Mod).notNode());
            conj.push_back(nm->mkNode(IMPLIES, noneqx, difference));
          }
        }
        // and lemmas
        Node lem = conj.size() == 1 ? conj[0] : nm->mkNode(AND, conj);
        Trace("piand-lemma") << "PIAndSolver::Lemma: " << lem << " ; INIT_REFINE"
                            << std::endl;
        d_im.addPendingLemma(lem, InferenceId::ARITH_NL_PIAND_INIT_REFINE);
      }
      // skolem lemmas
      if (options().smt.PiandSkolem) {
        // x = 100...0 => piand(k,x,y) = 0 \/ x
        Node skolem = sm->mkDummySkolem("expVar_"+ std::to_string(skolem_num), nm->integerType());
        skolem_num++;
        Node pow2_skolem = nm->mkNode(kind::POW2, skolem);
        Node pow2_skolem_eq_x = nm->mkNode(kind::EQUAL, pow2_skolem, x);
        Node i_eq_zero = nm->mkNode(kind::EQUAL, i, d_zero);
        Node i_eq_x = nm->mkNode(kind::EQUAL, i, arg0Mod);
        Node or_res = nm->mkNode(kind::OR, i_eq_zero, i_eq_x);
        Node ite_skolem = nm->mkNode(kind::IMPLIES, pow2_skolem_eq_x, or_res);
        Node skolem_low_bound = nm->mkNode(kind::GEQ, skolem, d_zero);
        Node skolem_upper_bound = nm->mkNode(kind::LT, skolem, k);
        Node skolem_lemma = nm->mkNode(kind::AND, skolem_low_bound, skolem_upper_bound, ite_skolem);
        d_im.addPendingLemma(skolem_lemma, InferenceId::ARITH_NL_PIAND_SUM_REFINE, nullptr, true);
        // y = 100...0 => piand(k,x,y) = 0 \/ y
        Node pow2_skolem_eq_y = nm->mkNode(kind::EQUAL, pow2_skolem, arg1Mod);
        Node i_eq_y = nm->mkNode(kind::EQUAL, i, arg1Mod);
        Node or_res_y = nm->mkNode(kind::OR, i_eq_zero, i_eq_y);
        Node ite_skolem_y = nm->mkNode(kind::IMPLIES, pow2_skolem_eq_y, or_res_y);
        Node skolem_lemma_y = nm->mkNode(kind::AND, skolem_low_bound, skolem_upper_bound, ite_skolem_y);
        d_im.addPendingLemma(skolem_lemma_y, InferenceId::ARITH_NL_PIAND_SUM_REFINE, nullptr, true);
      }
    }
  }
}

void PIAndSolver::checkFullRefine()
{
  // std::cout << "full: " << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  Trace("piand-check") << "PIAndSolver::checkFullRefine";
  Trace("piand-check") << "PIAND terms: " << std::endl;
  for (const std::pair<Node, std::vector<Node> >& is : d_piands)
  {
    int index = 0;
    for (const Node& i : is.second)
    {
      index++;
      Node valAndXY = d_model.computeAbstractModelValue(i);
      Node valAndXYC = d_model.computeConcreteModelValue(i);

      Node k = i[0];
      Node x = i[1];
      Node y = i[2];
      Node valK = d_model.computeConcreteModelValue(k);
      Node valX = d_model.computeConcreteModelValue(x);
      Node valY = d_model.computeConcreteModelValue(y);

      Integer model_piand = valAndXYC.getConst<Rational>().getNumerator();
      Integer model_k = valK.getConst<Rational>().getNumerator();
      Integer model_x = valX.getConst<Rational>().getNumerator();
      Integer model_y = valY.getConst<Rational>().getNumerator();
      

      if (TraceIsOn("piand-check"))
      {
        Trace("piand-check")
            << "* " << i << ", value = " << valAndXY << std::endl;
        Trace("piand-check") << "  actual (" << valX << ", " << valY
                            << ") = " << valAndXYC << std::endl;
      }
      if (valAndXY == valAndXYC)
      {
        Trace("piand-check") << "...already correct" << std::endl;
        continue;
      }

      // ************* additional lemma schemas go here
      if (options().smt.PiandLemmasMode == options::PIandLemmasMode::SUM) {
        Node sum_eq = sumBasedLemma(i, EQUAL);
        d_im.addPendingLemma(
              sum_eq, InferenceId::ARITH_NL_PIAND_SUM_REFINE, nullptr, true);
      } else if (options().smt.PiandLemmasMode == options::PIandLemmasMode::SUM_GE) {
        Node lem_sum = sumBasedLemma(i, GEQ);
        d_im.addPendingLemma(
              lem_sum, InferenceId::ARITH_NL_PIAND_SUM_REFINE, nullptr, true);
      } else if (options().smt.PiandLemmasMode == options::PIandLemmasMode::SUM_BOTH) {
        Node lem_sum = sumBasedLemma(i, EQUAL);
        d_im.addPendingLemma(
              lem_sum, InferenceId::ARITH_NL_PIAND_SUM_REFINE, nullptr, true);
        Node sum_gt = sumBasedLemma(i, GEQ);
        d_im.addPendingLemma(
              sum_gt, InferenceId::ARITH_NL_PIAND_SUM_REFINE, nullptr, true);
      } else if (options().smt.PiandLemmasMode == options::PIandLemmasMode::BITWISE) {
        Node lem_bit = bitwiseLemma(i);
        d_im.addPendingLemma(
            lem_bit, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
      }

      
      Integer ione = 1;
      Integer itwo = 2;
      Integer ipow2 = itwo.pow(model_k.getLong());
      Integer max_int = ipow2 - 1;
      Node k_gt_0 = nm->mkNode(kind::GT, k, d_zero);
      Node twok = nm->mkNode(kind::POW2, k);
      Node arg0Mod = nm->mkNode(kind::INTS_MODULUS, x, twok);
      Node arg1Mod = nm->mkNode(kind::INTS_MODULUS, y, twok);
      Node arg0Mod2 = nm->mkNode(kind::INTS_MODULUS, x, d_two);
      Node arg1Mod2 = nm->mkNode(kind::INTS_MODULUS, y, d_two);
      if (options().smt.PiandMode == options::PIandMode::PIAND || options().smt.PiandMode == options::PIandMode::PIAND_OPT)  {
        // base case: piand(k,1,1) = 1
        if (model_k > 0 && model_x == 1 && model_y == 1 && model_piand != 1) {
          Node x_equal_one = nm->mkNode(EQUAL, x, d_one);
          Node y_equal_one = nm->mkNode(EQUAL, y, d_one);
          Node assum = nm->mkNode(kind::AND, k_gt_0, x_equal_one, y_equal_one);
          Node piand_one = nm->mkNode(EQUAL, i, d_one);
          Node xy_one_lem = nm->mkNode(IMPLIES, assum, piand_one);
          d_im.addPendingLemma(
              xy_one_lem, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
        }

        // difference: x != x2 /\ y = y2 => piand(x,y) != x2 \/ piand(x2, y2) != x 
        Node x_geq_zero = nm->mkNode(kind::GEQ, x, d_zero);
        Node x_lt_pow2 = nm->mkNode(LT, x, twok);
        Node x_range = nm->mkNode(AND, x_geq_zero, x_lt_pow2);
        Node y_geq_zero = nm->mkNode(kind::GEQ, y, d_zero);
        Node y_lt_pow2 = nm->mkNode(LT, y, twok);
        Node y_range = nm->mkNode(AND, y_geq_zero, y_lt_pow2);
        if (options().smt.PiandDifference) {
          int j = -1;
          for (const Node& n : is.second)
          {
            j++;
            if(j > index) {
              Node k2 = n[0];
              Node x2 = n[1];
              Node y2 = n[2];
              Node valK2 = d_model.computeConcreteModelValue(k2);
              Node valX2 = d_model.computeConcreteModelValue(x2);
              Node valY2 = d_model.computeConcreteModelValue(y2);
              Node valAndXYC2 = d_model.computeConcreteModelValue(n);
              Integer model_piand2 = valAndXYC2.getConst<Rational>().getNumerator();
              Integer model_k2 = valK2.getConst<Rational>().getNumerator();
              Integer model_x2 = valX2.getConst<Rational>().getNumerator();
              Integer model_y2 = valY2.getConst<Rational>().getNumerator();

              Node arg20Mod = nm->mkNode(kind::INTS_MODULUS, x2, twok);
              Node arg21Mod = nm->mkNode(kind::INTS_MODULUS, y2, twok);

              Node x2_geq_zero = nm->mkNode(kind::GEQ, x2, d_zero);
              Node x2_lt_pow2 = nm->mkNode(LT, x2, twok);
              Node x2_range = nm->mkNode(AND, x2_geq_zero, x2_lt_pow2);

              if (model_k > 0 && model_k == model_k2 && model_x != model_x2 && model_y == model_y2 && model_piand == model_x2 && model_piand2 == model_x) {
                Node noneqx = nm->mkNode(AND, k.eqNode(k2), (x.eqNode(x2)).notNode(), y.eqNode(y2));
                Node ranges_assum = nm->mkNode(AND, x_range, x2_range, y_range);
                Node assum_difference = nm->mkNode(AND, k_gt_0, noneqx, ranges_assum);
                if (options().smt.PiandMode == options::PIandMode::PIAND_OPT) {
                  assum_difference = noneqx;
                }
                Node difference = nm->mkNode(OR, i.eqNode(x2).notNode(), n.eqNode(x).notNode());
                Node diff_lemm = nm->mkNode(IMPLIES, assum_difference, difference);
                d_im.addPendingLemma(
                  diff_lemm, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
              }
            } 
      
          }
        }

        // contradition: x+y mod 2^k = 2^k-1 => piand(x,y) = 0
        if (model_x + model_y == max_int && model_piand != 0) {
          Node x_plus_y = nm->mkNode(kind::ADD, x, y);
          Node x_plus_y_mod = nm->mkNode(kind::INTS_MODULUS, x_plus_y, twok);
          Node twok_minus_one = nm->mkNode(kind::SUB, twok, d_one);
          Node assum = nm->mkNode(kind::EQUAL, x_plus_y_mod, twok_minus_one);
          if (options().smt.PiandMode == options::PIandMode::PIAND_OPT) {
            assum = nm->mkNode(kind::EQUAL, x_plus_y, twok_minus_one);
          }
          Node piand_zero = nm->mkNode(EQUAL, i, d_zero);
          Node neg_lem = nm->mkNode(IMPLIES, assum, piand_zero);
          d_im.addPendingLemma(
                  neg_lem, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
        }

        //lsb and: k > 0 && y mod 2^k = 1 -> piand(k,x,y) = x % 2
        if (model_k > 0 && model_y == 1 && model_piand != model_x.modByPow2(1)) {
          Node y_equal_one = nm->mkNode(EQUAL, y, d_one);
          Node asuum_lsb = nm->mkNode(AND, k_gt_0, y_equal_one);
          if (options().smt.PiandMode == options::PIandMode::PIAND_OPT) {
            asuum_lsb = y_equal_one;
          }
          Node lsb = nm->mkNode(EQUAL, i, arg0Mod2);
          Node y_one_lem = nm->mkNode(IMPLIES, asuum_lsb, lsb);
          d_im.addPendingLemma(
              y_one_lem, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
        }  

        //lsb and: k > 0 && x mod 2^k = 1 -> piand(k,x,y) = y % 2
        if (model_k > 0 && model_x == 1 && model_piand != model_y.modByPow2(1)) {
          Node x_equal_one = nm->mkNode(EQUAL, x, d_one);
          Node asuum_lsb2 = nm->mkNode(AND, k_gt_0, x_equal_one);
          if (options().smt.PiandMode == options::PIandMode::PIAND_OPT) {
            asuum_lsb2 = x_equal_one;
          }
          Node lsb2 = nm->mkNode(EQUAL, i, arg1Mod2);
          Node x_one_lem = nm->mkNode(IMPLIES, asuum_lsb2, lsb2);
          d_im.addPendingLemma(
            x_one_lem, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
        }  
       
      } else if (options().smt.PiandMode == options::PIandMode::CEGAR) {
          // 0 <= piand(x,y)
          if (model_piand < 0) {
            Node min_bound = nm->mkNode(LEQ, d_zero, i);
            d_im.addPendingLemma(
                  min_bound, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
          }
          // piand(x,y)<=mod(x, 2^k) && piand(x,y)<=mod(y, 2^k)
          if (model_piand > model_x || model_piand > model_y) {
            Node x_lt_y = nm->mkNode(kind::LT, arg0Mod, arg1Mod);
            Node piand_lt_x = nm->mkNode(LEQ, i, arg0Mod);
            Node piand_lt_y = nm->mkNode(LEQ, i, arg1Mod);
            Node max_range = nm->mkNode(kind::ITE, x_lt_y, piand_lt_x, piand_lt_y);
            d_im.addPendingLemma(
                  max_range, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
          }
          // piand(x,y) = piand(y,x)
          Node piand_y_x = nm->mkNode(kind::PIAND, k, valY, valX);
          Node piand_x_y = nm->mkNode(kind::PIAND, k, valX, valY);
          Node sim_lemma = nm->mkNode(kind::EQUAL, piand_x_y,  piand_y_x);
          d_im.addPendingLemma(
                  sim_lemma, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
          // piand(x,x) = x
          if(model_x == model_y && model_piand != model_x) {
            Node eq_y_x = nm->mkNode(kind::EQUAL, arg1Mod, arg0Mod);
            Node idempotence_lemma = nm->mkNode(kind::IMPLIES, eq_y_x,  i.eqNode(arg0Mod));
            d_im.addPendingLemma(
                  idempotence_lemma, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
          }
          // piand(x,0) = 0
          if (model_y == 0 && model_piand != 0) {
            Node eq_y_zero = nm->mkNode(kind::EQUAL, y, d_zero);
            Node zero_lemma = nm->mkNode(kind::IMPLIES, eq_y_zero,  i.eqNode(d_zero));
            d_im.addPendingLemma(
                  zero_lemma, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
          }
          // piand(x,max)=x
          if (model_y == max_int && model_piand != model_x) {
            Node pow2_k = nm->mkNode(kind::POW2, k);
            Node pow2_k_minus_one = nm->mkNode(kind::SUB, pow2_k, d_one);
            Node eq_y_max = nm->mkNode(kind::EQUAL, arg1Mod, pow2_k_minus_one);
            Node max_lemma = nm->mkNode(kind::IMPLIES, eq_y_max, i.eqNode(arg0Mod));
            d_im.addPendingLemma(
                  max_lemma, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
          }
          // x+y = 2^k-1 => piand(x,y) = 0
          if (model_x + model_y == max_int && model_piand != 0) {
            Node plus_xy = nm->mkNode(kind::ADD , arg0Mod, arg1Mod);
            Node pow2_k = nm->mkNode(kind::POW2, k);
            Node pow2_k_minus_one = nm->mkNode(kind::SUB, pow2_k, d_one);  
            Node conjection_lemma = nm->mkNode(IMPLIES, plus_xy.eqNode(pow2_k_minus_one), i.eqNode(d_zero));
            d_im.addPendingLemma(
                  conjection_lemma, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
          }
          // piand(1,x,y) = min(ex0(x), ex0(y))
          if (model_k == 1 && model_piand > 1) {
            Node k_eq_one = nm->mkNode(kind::EQUAL, k, d_one);
            Node arg0Mod2_big = nm->mkNode(kind::GEQ, arg0Mod2, arg1Mod2);
            Node min_ex0 = nm->mkNode(kind::ITE, arg0Mod2_big, arg0Mod2, arg1Mod2);
            Node min_lemma = nm->mkNode(kind::IMPLIES, k_eq_one,  min_ex0);
            d_im.addPendingLemma(
                    min_lemma, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
          }
          // difference: x != x2 /\ y = y2 => piand(x,y) != x2 \/ piand(x2, y2) != x 
          int j = -1;
          for (const Node& n : is.second)
          {
            j++;
            if(j > index) {
              Node x2 = n[1];
              Node y2 = n[2];
              Node valX2 = d_model.computeConcreteModelValue(x2);
              Node valY2 = d_model.computeConcreteModelValue(y2);
              Node valAndXYC2 = d_model.computeConcreteModelValue(n);
              Integer model_piand2 = valAndXYC2.getConst<Rational>().getNumerator();
              Integer model_x2 = valX2.getConst<Rational>().getNumerator();
              Integer model_y2 = valY2.getConst<Rational>().getNumerator();
              if (model_x != model_x2 && model_y == model_y2 && (model_piand == model_x2 || model_piand2 == model_x)) {
                Node power2_k = nm->mkNode(kind::POW2, k);
                Node arg20Mod = nm->mkNode(kind::INTS_MODULUS, x2, power2_k);
                Node arg21Mod = nm->mkNode(kind::INTS_MODULUS, y2, power2_k);
                Node noneqx = nm->mkNode(AND, (arg0Mod.eqNode(arg20Mod)).notNode(), arg1Mod.eqNode(arg21Mod));
                Node difference = nm->mkNode(OR, i.eqNode(arg20Mod).notNode(), n.eqNode(arg0Mod).notNode());
                Node diff_lemma = nm->mkNode(IMPLIES, noneqx, difference);
                d_im.addPendingLemma(
                      diff_lemma, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
              }
            }
          }
      }
    }
  }
}

Node PIAndSolver::valueBasedLemma(Node i)
{
  Assert(i.getKind() == PIAND);

  Node k = i[0];
  Node x = i[1];
  Node y = i[2];

  Node valK = d_model.computeConcreteModelValue(k);
  Node valX = d_model.computeConcreteModelValue(x);
  Node valY = d_model.computeConcreteModelValue(y);

  NodeManager* nm = NodeManager::currentNM();
  Node valC = nm->mkNode(PIAND, valK, valX, valY);

  valC = rewrite(valC);
  Node lem = nm->mkNode(
      IMPLIES, nm->mkNode(AND, k.eqNode(valK), x.eqNode(valX), y.eqNode(valY)), i.eqNode(valC));
  return lem;
}


static Rational intpow2(uint64_t b)
{
  return Rational(Integer(2).pow(b), Integer(1));
}

Node PIAndSolver::sumBasedLemma(Node i, Kind kind)
{
  Assert(i.getKind() == PIAND);
  Node k = d_model.computeConcreteModelValue(i[0]);
  Node x = i[1];
  Node y = i[2];
  uint64_t granularity = options().smt.BVAndIntegerGranularity;
  uint64_t int_k =  k.getConst<Rational>().getNumerator().toUnsignedInt();
  // Integer int_k = k.getConst<Rational>().getNumerator().toUnsignedInt();
  NodeManager* nm = NodeManager::currentNM();
  // i[0] = k => i = sum
  Node width = nm->mkNode(kind, i[0], k);
  Node condition;
  if (kind == GEQ || kind == GT) {
    kind = EQUAL;
    Node pow2_k = nm->mkConstInt(Integer(2).pow(int_k));
    Node zero = nm->mkConstInt(Rational(0));
    Node x_pos = nm->mkNode(GEQ, x, zero);
    Node y_pos = nm->mkNode(GEQ, y, zero);
    Node x_lt_pow2 = nm->mkNode(LT, x, pow2_k);
    Node y_lt_pow2 = nm->mkNode(LT, y, pow2_k);
    Node bound_x = nm->mkNode(AND, x_lt_pow2, x_pos);
    Node bound_y = nm->mkNode(AND, y_lt_pow2, y_pos);
    condition = nm->mkNode(AND, bound_x, width);
  } 
  if (kind == EQUAL) {
    condition = width;
  }
  Node then = nm->mkNode(EQUAL, i, d_iandUtils.createSumNode(x, y, int_k, granularity));
  Node lem = nm->mkNode(IMPLIES, condition, then);
  return lem;
}

Node PIAndSolver::bitwiseLemma(Node i)
{
  Assert(i.getKind() == PIAND);
  Node k = d_model.computeConcreteModelValue(i[0]);
  Node x = i[1];
  Node y = i[2];
  
  // unsigned bvsize = std::stoul(k.toString());
  unsigned bvsize = k.getConst<Rational>().getNumerator().toUnsignedInt();
  uint64_t granularity = options().smt.BVAndIntegerGranularity;

  Rational absI = d_model.computeAbstractModelValue(i).getConst<Rational>();
  Rational concI = d_model.computeConcreteModelValue(i).getConst<Rational>();

  Assert(absI.isIntegral());
  Assert(concI.isIntegral());

  BitVector bvAbsI = BitVector(bvsize, absI.getNumerator());
  BitVector bvConcI = BitVector(bvsize, concI.getNumerator());

  NodeManager* nm = NodeManager::currentNM();
  Node lem = d_true;

  // compare each bit to bvI
  Node cond;
  Node bitIAnd;
  uint64_t high_bit;
  for (uint64_t j = 0; j < bvsize; j += granularity)
  {
    high_bit = j + granularity - 1;
    // don't let high_bit pass bvsize
    if (high_bit >= bvsize)
    {
      high_bit = bvsize - 1;
    }

    // check if the abstraction differs from the concrete one on these bits
    if (bvAbsI.extract(high_bit, j) != bvConcI.extract(high_bit, j))
    {
      bitIAnd = d_iandUtils.createBitwiseIAndNode(x, y, high_bit, j);
      // enforce bitwise equality
      lem = nm->mkNode(
          AND,
          lem,
          rewrite(d_iandUtils.iextract(high_bit, j, i)).eqNode(bitIAnd));
    }
  }
  return lem;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal