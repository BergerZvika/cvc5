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
  Trace("piand-check") << "PIAndSolver::checkInitialRefine" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  int j;
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
      Node arg1Mod2 = nm->mkNode(kind::INTS_MODULUS, x, d_two);
      Node plus = nm->mkNode(kind::ADD , arg0Mod, arg1Mod);
      Node twok_minus_one = nm->mkNode(kind::SUB, twok, d_one);
      // initial refinement lemmas
      std::vector<Node> conj;
      Assert(x <= y);
      // 0 <= piand(x,y)
      conj.push_back(nm->mkNode(LEQ, d_zero, i));
      // piand(x,y)<=mod(x, 2^k)
      conj.push_back(nm->mkNode(LEQ, i, arg0Mod));
      // piand(x,y)<=mod(y, 2^k)
      conj.push_back(nm->mkNode(LEQ, i, arg1Mod));
      // x=y => piand(x,y)=mod(x, 2^k)
      conj.push_back(nm->mkNode(IMPLIES, x.eqNode(y), i.eqNode(arg0Mod)));
      // x+y = 2^k-1 => piand(x,y) = 0
      conj.push_back(nm->mkNode(IMPLIES, plus.eqNode(twok_minus_one), i.eqNode(d_zero)));
      // k <= 0 -> piand (k, x, y) = 0 
      Node nonegative = nm->mkNode(LEQ, k, d_zero);
      Node equal_zero = nm->mkNode(EQUAL, i, d_zero);
      conj.push_back(nm->mkNode(IMPLIES, nonegative, equal_zero));
      j = -1;
      for (const Node& n : is.second)
      {
        j++;
        if(j > index) {
          Node x2 = n[1];
          Node y2 = n[2];
          if (options().smt.PiandDifference) {
            // difference: x != x2 /\ y = y2 => piand(x,y) != x2 \/ piand(x2, y2) != x 
            Node noneqx = nm->mkNode(AND, (x.eqNode(x2)).notNode(), y.eqNode(y2));
            Node difference = nm->mkNode(OR, i.eqNode(x2).notNode(), n.eqNode(x).notNode());
            conj.push_back(nm->mkNode(IMPLIES, noneqx, difference));
          } 
          else {
            // x = x2 /\ y = y2 => piand(k,x,y) = piand (k2,x2,y2)
            Node eqxy = nm->mkNode(AND, (x.eqNode(x2)), y.eqNode(y2));
            conj.push_back(nm->mkNode(IMPLIES, eqxy, i.eqNode(n)));
          }
        }
      }
      // even lemmas: x % 2 = 0 => piand(k,x,y) % 2 = 0
      Node arg0Mod2_eq_zero = nm->mkNode(kind::EQUAL, arg0Mod2, d_zero);
      Node piand_mod_two = nm->mkNode(kind::INTS_MODULUS, i, d_two);
      conj.push_back(nm->mkNode(IMPLIES, arg0Mod2_eq_zero, piand_mod_two.eqNode(d_zero)));
      Node arg1Mod2_eq_zero = nm->mkNode(kind::EQUAL, arg1Mod2, d_zero);
      conj.push_back(nm->mkNode(IMPLIES, arg1Mod2_eq_zero, piand_mod_two.eqNode(d_zero)));
      // // odd lemma: x % 2 = 1 /\ y % 2 = 1  => piand(k,x,y) % 2 = 1 
      // Node arg0Mod2_eq_one = nm->mkNode(kind::EQUAL, arg0Mod2, d_one);
      // Node arg1Mod2_eq_one = nm->mkNode(kind::EQUAL, arg1Mod2, d_one);
      // Node and_odd = nm->mkNode(kind::AND, arg0Mod2_eq_one, arg1Mod2_eq_one);
      // conj.push_back(nm->mkNode(IMPLIES, and_odd, piand_mod_two.eqNode(d_one)));
      // insert lemmas
      Node lem = conj.size() == 1 ? conj[0] : nm->mkNode(AND, conj);
      Trace("piand-lemma") << "PIAndSolver::Lemma: " << lem << " ; INIT_REFINE"
                          << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_PIAND_INIT_REFINE);

      // skolem lemmas
      if (options().smt.PiandSkolem) {
        // x = 100...0 => piand(k,x,y) = 0 \/ x
        Node skolem = sm->mkDummySkolem("expVar_"+ std::to_string(skolem_num), nm->integerType());
        skolem_num++;
        Node pow2_skolem = nm->mkNode(kind::POW2, skolem);
        Node pow2_skolem_eq_x = nm->mkNode(kind::EQUAL, pow2_skolem, arg0Mod);
        Node i_eq_zero = nm->mkNode(kind::EQUAL, i, d_zero);
        Node i_eq_x = nm->mkNode(kind::EQUAL, i, arg0Mod);
        Node or_res = nm->mkNode(kind::OR, i_eq_zero, i_eq_x);
        Node ite_skolem = nm->mkNode(kind::ITE, pow2_skolem_eq_x, or_res);
        Node skolem_low_bound = nm->mkNode(kind::GEQ, skolem, d_zero);
        Node skolem_upper_bound = nm->mkNode(kind::LT, skolem, k);
        Node skolem_lemma = nm->mkNode(kind::AND, skolem_low_bound, skolem_upper_bound, ite_skolem);
        d_im.addPendingLemma(skolem_lemma, InferenceId::ARITH_NL_PIAND_SUM_REFINE, nullptr, true);
        // y = 100...0 => piand(k,x,y) = 0 \/ y
        Node pow2_skolem_eq_y = nm->mkNode(kind::EQUAL, pow2_skolem, arg1Mod);
        Node i_eq_y = nm->mkNode(kind::EQUAL, i, arg1Mod);
        Node or_res_y = nm->mkNode(kind::OR, i_eq_zero, i_eq_y);
        Node ite_skolem_y = nm->mkNode(kind::ITE, pow2_skolem_eq_y, or_res_y);
        Node skolem_lemma_y = nm->mkNode(kind::AND, skolem_low_bound, skolem_upper_bound, ite_skolem_y);
        d_im.addPendingLemma(skolem_lemma_y, InferenceId::ARITH_NL_PIAND_SUM_REFINE, nullptr, true);
        // pow2(s) > x => 
      }
    }
  }
}

void PIAndSolver::checkFullRefine()
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("piand-check") << "PIAndSolver::checkFullRefine";
  Trace("piand-check") << "PIAND terms: " << std::endl;
  for (const std::pair<Node, std::vector<Node> >& is : d_piands)
  {
    int index = 0;
    // int j = 0;
    // the reference bitwidth
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

      // int model_x = std::stoi(valX.getConst<Rational>().getNumerator().toString());
      // int model_y = std::stoi(valY.getConst<Rational>().getNumerator().toString());
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

      if (options().smt.PiandMode == options::PIandMode::SUM) {
        Node sum_eq = sumBasedLemma(i, EQUAL);
        d_im.addPendingLemma(
              sum_eq, InferenceId::ARITH_NL_PIAND_SUM_REFINE, nullptr, true);
        Node sum_gt = sumBasedLemma(i, GT);
        d_im.addPendingLemma(
              sum_gt, InferenceId::ARITH_NL_PIAND_SUM_REFINE, nullptr, true);
      } else if (options().smt.PiandMode == options::PIandMode::SUM_GE) {
        Node lem_sum = sumBasedLemma(i, GEQ);
        d_im.addPendingLemma(
              lem_sum, InferenceId::ARITH_NL_PIAND_SUM_REFINE, nullptr, true);
      } else if (options().smt.PiandMode == options::PIandMode::SUM_EQ) {
        Node lem_sum = sumBasedLemma(i, EQUAL);
        d_im.addPendingLemma(
              lem_sum, InferenceId::ARITH_NL_PIAND_SUM_REFINE, nullptr, true);
      } else if (options().smt.PiandMode == options::PIandMode::BITWISE) {
        Node lem_bit = bitwiseLemma(i);
        d_im.addPendingLemma(
             lem_bit, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
      }

      // for (const Node& n : is.second)
      // {
      //   j++;
      //   if(j > index) {
      //     Node x2 = n[1];
      //     Node y2 = n[2];

      //     Node valAndXY2 = d_model.computeAbstractModelValue(n);
      //     Node valX2 = d_model.computeConcreteModelValue(x2);
      //     Node valY2 = d_model.computeConcreteModelValue(y2);

      //     int model_x2 = std::stoi(valX2.getConst<Rational>().getNumerator().toString());
      //     int model_y2 = std::stoi(valY2.getConst<Rational>().getNumerator().toString());
      //     int model_piand2;
      //     try {
      //       model_piand = std::stoi(valAndXY2.getConst<Rational>().getNumerator().toString());
      //     } catch (...) {
      //       model_piand2 = -1;
      //     }
      //     if (model_piand2 != -1 && model_piand != -1) {
      //       // difference: x != x2 /\ y = y2 => piand(x,y) != x2 \/ piand(x2, y2) != x 
      //       if (model_x != model_x2 && model_y == model_y2 && (model_piand == model_x2 || model_piand2 == model_x)) {
      //         Node noneqx = nm->mkNode(AND, (x.eqNode(x2)).notNode(), y.eqNode(y2));
      //         Node difference = nm->mkNode(OR, i.eqNode(x2).notNode(), n.eqNode(x).notNode());
      //         Node diff_lem = nm->mkNode(IMPLIES, noneqx, difference);
      //         d_im.addPendingLemma(
      //           diff_lem, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
      //       }
      //       // x = x2 /\ y = y2 => piand(k,x,y) = piand (k2,x2,y2)
      //       if (model_x == model_x2 && model_y == model_y2 && model_piand != model_piand2) {
      //         Node eqxy = nm->mkNode(AND, (x.eqNode(x2)), y.eqNode(y2));
      //         Node eq_lem = nm->mkNode(IMPLIES, eqxy, i.eqNode(n));
      //         d_im.addPendingLemma(
      //           eq_lem, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
      //       }
      //     }
          
      //   }
      // }

        // piand(k,x,1) = x % 2
      if (model_y == 1) {
            Node y_equal_one = nm->mkNode(EQUAL, y, d_one);
            Node arg0Mod2 = nm->mkNode(kind::INTS_MODULUS, x, d_two);
            Node lsb = nm->mkNode(EQUAL, i, arg0Mod2);
            Node y_one_lem = nm->mkNode(IMPLIES, y_equal_one, lsb);
            d_im.addPendingLemma(
                y_one_lem, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
      }

      if (model_x == 1) {
            Node x_equal_one = nm->mkNode(EQUAL, x, d_one);
            Node arg1Mod2 = nm->mkNode(kind::INTS_MODULUS, y, d_two);
            Node lsb = nm->mkNode(EQUAL, i, arg1Mod2);
            Node y_one_lem = nm->mkNode(IMPLIES, x_equal_one, lsb);
            d_im.addPendingLemma(
                y_one_lem, InferenceId::ARITH_NL_PIAND_BITWISE_REFINE, nullptr, true);
        }
      
      // // odd lemma: x % 2 = 1 /\ y % 2 = 1  => piand(k,x,y) % 2 = 1 
      // Node arg0Mod2_eq_one = nm->mkNode(kind::EQUAL, arg0Mod2, d_one);
      // Node arg1Mod2_eq_one = nm->mkNode(kind::EQUAL, arg1Mod2, d_one);
      // Node and_odd = nm->mkNode(kind::AND, arg0Mod2_eq_one, arg1Mod2_eq_one);
      // conj.push_back(nm->mkNode(IMPLIES, and_odd, piand_mod_two.eqNode(d_one)));

      // if (model_x % 2 == 0) {
        
      // }
      // if (model_y % 2 == 0) {
        
      // }
      // if (model_y % 2 == 1 && model_x % 2 == 1) {
        
      // }

      // this is the most naive model-based schema based on model values
      Node lem = valueBasedLemma(i);
      Trace("piand-lemma")
            << "PIAndSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
      // send the value lemma
      d_im.addPendingLemma(lem,
                    InferenceId::ARITH_NL_PIAND_VALUE_REFINE,
                    nullptr,
                    true);
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

Node PIAndSolver::sumBasedLemma(Node i, Kind kind)
{
  Assert(i.getKind() == PIAND);
  Node k = d_model.computeConcreteModelValue(i[0]);
  Node x = i[1];
  Node y = i[2];
  uint64_t granularity = options().smt.BVAndIntegerGranularity;
  NodeManager* nm = NodeManager::currentNM();
  // i[0] = k => i = sum
  Node width = nm->mkNode(kind, i[0], k);
  Node then = nm->mkNode(kind, i, d_iandUtils.createSumNode(x, y, std::stoul(k.toString()), granularity));
  Node lem = nm->mkNode(IMPLIES, width, then);
  return lem;
}

Node PIAndSolver::bitwiseLemma(Node i)
{
  Assert(i.getKind() == PIAND);
  Node k = d_model.computeConcreteModelValue(i[0]);
  Node x = i[1];
  Node y = i[2];

  unsigned bvsize = std::stoul(k.toString());
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
