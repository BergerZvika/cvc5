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
//#include "util/iand.h"

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
    // size_t bsize = a.getOperator().getConst<IntAnd>().d_size;
    d_piands[a[0]].push_back(a);
  }

  Trace("piand") << "We have " << d_piands.size() << " PIAND terms." << std::endl;
}

void PIAndSolver::checkInitialRefine()
{
  Trace("piand-check") << "PIAndSolver::checkInitialRefine" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<Node, std::vector<Node> >& is : d_piands)
  {
    // the reference bitwidth
    Node k = is.first;
    for (const Node& i : is.second)
    {
      if (d_initRefine.find(i) != d_initRefine.end())
      {
        // already sent initial axioms for i in this user context
        continue;
      }
      d_initRefine.insert(i);
      // Node op = i.getOperator();
      // size_t bsize = op.getConst<IntAnd>().d_size;
      // Node twok = nm->mkConstInt(Rational(Integer(2).pow(bsize)));
      Node twok = nm->mkNode(kind::POW2, k);
      Node arg0Mod = nm->mkNode(kind::INTS_MODULUS, i[0], twok);
      Node arg1Mod = nm->mkNode(kind::INTS_MODULUS, i[1], twok);
      // initial refinement lemmas
      std::vector<Node> conj;
      // piand(x,y)=piand(y,x) is guaranteed by rewriting
      Assert(i[0] <= i[1]);
      // 0 <= piand(x,y) < 2^k
      conj.push_back(nm->mkNode(LEQ, d_zero, i));
      // conj.push_back(nm->mkNode(LT, i, rewrite(d_iandUtils.twoToK(k))));
      conj.push_back(nm->mkNode(LT, i, twok));
      // piand(x,y)<=mod(x, 2^k)
      conj.push_back(nm->mkNode(LEQ, i, arg0Mod));
      // piand(x,y)<=mod(y, 2^k)
      conj.push_back(nm->mkNode(LEQ, i, arg1Mod));
      // x=y => piand(x,y)=mod(x, 2^k)
      conj.push_back(nm->mkNode(IMPLIES, i[0].eqNode(i[1]), i.eqNode(arg0Mod)));
      Node lem = conj.size() == 1 ? conj[0] : nm->mkNode(AND, conj);
      Trace("piand-lemma") << "PIAndSolver::Lemma: " << lem << " ; INIT_REFINE"
                          << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_PIAND_INIT_REFINE);
    }
  }
}

void PIAndSolver::checkFullRefine()
{
  Trace("piand-check") << "PIAndSolver::checkFullRefine";
  Trace("piand-check") << "PIAND terms: " << std::endl;
  for (const std::pair<Node, std::vector<Node> >& is : d_piands)
  {
    // the reference bitwidth
    Node k = is.first;
    for (const Node& i : is.second)
    {
      Node valAndXY = d_model.computeAbstractModelValue(i);
      Node valAndXYC = d_model.computeConcreteModelValue(i);
      if (TraceIsOn("piand-check"))
      {
        Node x = i[0];
        Node y = i[1];

        Node valX = d_model.computeConcreteModelValue(x);
        Node valY = d_model.computeConcreteModelValue(y);

        Trace("piand-check")
            << "* " << i << ", value = " << valAndXY << std::endl;
        Trace("piand-check") << "  actual (" << valX << ", " << valY
                            << ") = " << valAndXYC << std::endl;
        // print the bit-vector versions
        // Node bvalX = convertToBvK(k, valX);
        // Node bvalY = convertToBvK(k, valY);
        // Node bvalAndXY = convertToBvK(k, valAndXY);
        // Node bvalAndXYC = convertToBvK(k, valAndXYC);

        // Trace("piand-check") << "  bv-value = " << bvalAndXY << std::endl;
        // Trace("piand-check") << "  bv-actual (" << bvalX << ", " << bvalY
        //                     << ") = " << bvalAndXYC << std::endl;
      }
      if (valAndXY == valAndXYC)
      {
        Trace("piand-check") << "...already correct" << std::endl;
        continue;
      }

      // ************* additional lemma schemas go here
      // if (options().smt.iandMode == options::IandMode::SUM)
      // {
      //   Node lem = sumBasedLemma(i);  // add lemmas based on sum mode
      //   Trace("piand-lemma")
      //       << "PIAndSolver::Lemma: " << lem << " ; SUM_REFINE" << std::endl;
      //   // note that lemma can contain div/mod, and will be preprocessed in the
      //   // prop engine
      //   d_im.addPendingLemma(
      //       lem, InferenceId::ARITH_NL_PIAND_SUM_REFINE, nullptr, true);
      // }
      // else if (options().smt.iandMode == options::IandMode::BITWISE)
      // {
      //   Node lem = bitwiseLemma(i);  // check for violated bitwise axioms
      //   Trace("iand-lemma")
      //       << "IAndSolver::Lemma: " << lem << " ; BITWISE_REFINE" << std::endl;
      //   // note that lemma can contain div/mod, and will be preprocessed in the
      //   // prop engine
      //   d_im.addPendingLemma(
      //       lem, InferenceId::ARITH_NL_IAND_BITWISE_REFINE, nullptr, true);
      // }
      // else
      // {
        // this is the most naive model-based schema based on model values
        Node lem = valueBasedLemma(i);
        Trace("piand-lemma")
            << "PIAndSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
        // send the value lemma
        d_im.addPendingLemma(lem,
                             InferenceId::ARITH_NL_PIAND_VALUE_REFINE,
                             nullptr,
                             true);
      // }
    }
  }
}

// Node PIAndSolver::convertToBvK(unsigned k, Node n) const
// {
//   Assert(n.isConst() && n.getType().isInteger());
//   NodeManager* nm = NodeManager::currentNM();
//   Node iToBvOp = nm->mkConst(IntToBitVector(k));
//   Node bn = nm->mkNode(kind::INT_TO_BITVECTOR, iToBvOp, n);
//   return rewrite(bn);
// }

// Node PIAndSolver::mkIAnd(unsigned k, Node x, Node y) const
// {
//   NodeManager* nm = NodeManager::currentNM();
//   Node iAndOp = nm->mkConst(IntAnd(k));
//   Node ret = nm->mkNode(IAND, iAndOp, x, y);
//   ret = rewrite(ret);
//   return ret;
// }

// Node PIAndSolver::mkIOr(unsigned k, Node x, Node y) const
// {
//   Node ret = mkINot(k, mkIAnd(k, mkINot(k, x), mkINot(k, y)));
//   ret = rewrite(ret);
//   return ret;
// }

// Node PIAndSolver::mkINot(unsigned k, Node x) const
// {
//   NodeManager* nm = NodeManager::currentNM();
//   Node ret = nm->mkNode(SUB, d_iandUtils.twoToKMinusOne(k), x);
//   ret = rewrite(ret);
//   return ret;
// }

Node PIAndSolver::valueBasedLemma(Node i)
{
  Assert(i.getKind() == PIAND);
  Node x = i[0];
  Node y = i[1];

  Node valX = d_model.computeConcreteModelValue(x);
  Node valY = d_model.computeConcreteModelValue(y);

  NodeManager* nm = NodeManager::currentNM();
  Node valC = nm->mkNode(PIAND, i.getOperator(), valX, valY);
  valC = rewrite(valC);

  Node lem = nm->mkNode(
      IMPLIES, nm->mkNode(AND, x.eqNode(valX), y.eqNode(valY)), i.eqNode(valC));
  return lem;
}

// Node PIAndSolver::sumBasedLemma(Node i)
// {
//   Assert(i.getKind() == IAND);
//   Node x = i[0];
//   Node y = i[1];
//   size_t bvsize = i.getOperator().getConst<IntAnd>().d_size;
//   uint64_t granularity = options().smt.BVAndIntegerGranularity;
//   NodeManager* nm = NodeManager::currentNM();
//   Node lem = nm->mkNode(
//       EQUAL, i, d_iandUtils.createSumNode(x, y, bvsize, granularity));
//   return lem;
// }

// Node PIAndSolver::bitwiseLemma(Node i)
// {
//   Assert(i.getKind() == IAND);
//   Node x = i[0];
//   Node y = i[1];

//   unsigned bvsize = i.getOperator().getConst<IntAnd>().d_size;
//   uint64_t granularity = options().smt.BVAndIntegerGranularity;

//   Rational absI = d_model.computeAbstractModelValue(i).getConst<Rational>();
//   Rational concI = d_model.computeConcreteModelValue(i).getConst<Rational>();

//   Assert(absI.isIntegral());
//   Assert(concI.isIntegral());

//   BitVector bvAbsI = BitVector(bvsize, absI.getNumerator());
//   BitVector bvConcI = BitVector(bvsize, concI.getNumerator());

//   NodeManager* nm = NodeManager::currentNM();
//   Node lem = d_true;

//   // compare each bit to bvI
//   Node cond;
//   Node bitIAnd;
//   uint64_t high_bit;
//   for (uint64_t j = 0; j < bvsize; j += granularity)
//   {
//     high_bit = j + granularity - 1;
//     // don't let high_bit pass bvsize
//     if (high_bit >= bvsize)
//     {
//       high_bit = bvsize - 1;
//     }

//     // check if the abstraction differs from the concrete one on these bits
//     if (bvAbsI.extract(high_bit, j) != bvConcI.extract(high_bit, j))
//     {
//       bitIAnd = d_iandUtils.createBitwiseIAndNode(x, y, high_bit, j);
//       // enforce bitwise equality
//       lem = nm->mkNode(
//           AND,
//           lem,
//           rewrite(d_iandUtils.iextract(high_bit, j, i)).eqNode(bitIAnd));
//     }
//   }
//   return lem;
// }

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
