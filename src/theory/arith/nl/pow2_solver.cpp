/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Andres Noetzli, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of pow2 solver.
 */

#include "theory/arith/nl/pow2_solver.h"

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
#include <assert.h>

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

Pow2Solver::Pow2Solver(Env& env,
                       InferenceManager& im,
                       ArithState& state,
                       NlModel& model)
    : EnvObj(env), d_im(im), d_model(model), d_initRefine(userContext())
{
  NodeManager* nm = NodeManager::currentNM();
  d_false = nm->mkConst(false);
  d_true = nm->mkConst(true);
  d_zero = nm->mkConstInt(Rational(0));
  d_one = nm->mkConstInt(Rational(1));
  d_two = nm->mkConstInt(Rational(2));
}

Pow2Solver::~Pow2Solver() {}

void Pow2Solver::initLastCall(const std::vector<Node>& assertions,
                              const std::vector<Node>& false_asserts,
                              const std::vector<Node>& xts)
{
  d_pow2s.clear();
  Trace("pow2-mv") << "POW2 terms : " << std::endl;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    if (ak != POW2)
    {
      // don't care about other terms
      continue;
    }
    d_pow2s.push_back(a);
  }
  Trace("pow2") << "We have " << d_pow2s.size() << " pow2 terms." << std::endl;
}

void Pow2Solver::checkInitialRefine()
{
  Trace("pow2-check") << "Pow2Solver::checkInitialRefine" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (const Node& i : d_pow2s)
  {
    if (d_initRefine.find(i) != d_initRefine.end())
    {
      // already sent initial axioms for i in this user context
      continue;
    }
    d_initRefine.insert(i);
    // initial refinement lemmas
    std::vector<Node> conj;
    // x>=0 -> x < pow2(x)
    Node xgeq0 = nm->mkNode(LEQ, d_zero, i[0]);
    Node xltpow2x = nm->mkNode(LT, i[0], i);
    conj.push_back(nm->mkNode(IMPLIES, xgeq0, xltpow2x));
    // pow2(x) >= 0
    Node nonegative = nm->mkNode(GEQ, i , d_zero);
    conj.push_back(nonegative);
    // x>0 -> pow(2) mod 2 = 0
    Node xgt0 = nm->mkNode(LT, d_zero, i[0]);
    Node mod2 = nm->mkNode(INTS_MODULUS, i , d_two);
    Node even = nm->mkNode(EQUAL, mod2 , d_zero);
    conj.push_back(nm->mkNode(IMPLIES, xgt0, even));
    
    // x > 2 -> pow2(x) > x+x+1
    Node xgt2 = nm->mkNode(GT, i[0], d_two);
    Node two_times_x = nm->mkNode(ADD, i[0], i[0]);
    Node two_times_x_plus_one = nm->mkNode(ADD, two_times_x, d_one);
    Node low_bound = nm->mkNode(LT, two_times_x_plus_one, i);
    conj.push_back(nm->mkNode(IMPLIES, xgt2, low_bound));

    // x > 4 -> pow2(x) > x*x
    // Node four = nm->mkConstInt(Rational(4));
    // Node xgt4 = nm->mkNode(GT, i[0], four);
    // Node x_squar = nm->mkNode(MULT, i[0], i[0]);
    // Node low_bound2 = nm->mkNode(LT, x_squar, i);
    // conj.push_back(nm->mkNode(IMPLIES, xgt4, low_bound2));

    Node lem = nm->mkAnd(conj);
    Trace("pow2-lemma") << "Pow2Solver::Lemma: " << lem << " ; INIT_REFINE"
                        << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_POW2_INIT_REFINE);
  }
  
}

void Pow2Solver::sortPow2sBasedOnModel()
{
  struct
  {
    bool operator()(Node a, Node b, NlModel& model) const
    {
      return model.computeConcreteModelValue(a[0])
             < model.computeConcreteModelValue(b[0]);
    }
  } modelSort;
  using namespace std::placeholders;
  std::sort(
      d_pow2s.begin(), d_pow2s.end(), std::bind(modelSort, _1, _2, d_model));
}

void Pow2Solver::checkFullRefine()
{
  Trace("pow2-check") << "Pow2Solver::checkFullRefine" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  sortPow2sBasedOnModel();
  // add lemmas for each pow2 term
  for (uint64_t i = 0, size = d_pow2s.size(); i < size; i++)
  {
    Node n = d_pow2s[i];
    Node valPow2xAbstract = d_model.computeAbstractModelValue(n);
    Node valPow2xConcrete = d_model.computeConcreteModelValue(n);
    Node valXConcrete = d_model.computeConcreteModelValue(n[0]);
    if (TraceIsOn("pow2-check"))
    {
      Trace("pow2-check") << "* " << i << ", value = " << valPow2xAbstract
                          << std::endl;
      Trace("pow2-check") << "  actual " << valXConcrete << " = "
                          << valPow2xConcrete << std::endl;
    }
    if (valPow2xAbstract == valPow2xConcrete)
    {
      Trace("pow2-check") << "...already correct" << std::endl;
      continue;
    }

    Integer x = valXConcrete.getConst<Rational>().getNumerator();
    Integer pow2x = valPow2xAbstract.getConst<Rational>().getNumerator();
    // add monotinicity lemmas
    for (uint64_t j = i + 1; j < size; j++)
    {
      Node m = d_pow2s[j];
      Node valPow2yAbstract = d_model.computeAbstractModelValue(m);
      Node valYConcrete = d_model.computeConcreteModelValue(m[0]);

      Integer y = valYConcrete.getConst<Rational>().getNumerator();
      Integer pow2y = valPow2yAbstract.getConst<Rational>().getNumerator();

      if (x < y && pow2x >= pow2y)
      {
        Node assumption = nm->mkNode(LEQ, n[0], m[0]);
        Node conclusion = nm->mkNode(LEQ, n, m);
        Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
        d_im.addPendingLemma(
            lem, InferenceId::ARITH_NL_POW2_MONOTONE_REFINE, nullptr, true);
        }
    }

    // triviality lemmas: pow2(x) = 0 whenever x < 0
    if (x < 0 && pow2x != 0)
    {
      Node assumption = nm->mkNode(LT, n[0], d_zero);
      Node conclusion = nm->mkNode(EQUAL, n, d_zero);
      Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
      d_im.addPendingLemma(
          lem, InferenceId::ARITH_NL_POW2_TRIVIAL_CASE_REFINE, nullptr, true);
    }

    // Place holder for additional lemma schemas
    // assymptotic pow2 lemmas: k > 7 means x > k => pow2(x) > k^2x + k^2
    // assymptotic pow2 lemmas: k > 5 means x > k => pow2(x) > kx + k^2
    if (x > 5 && pow2x <= x*x*2)
        { 
          Node assumption = nm->mkNode(Kind::GT, n[0], valXConcrete);
          Node kx = nm->mkNode(Kind::MULT, valXConcrete, n[0]);
          Node k_squar = nm->mkNode(Kind::MULT, valXConcrete, valXConcrete);
          Node kx_plus_k_squar = nm->mkNode(Kind::ADD, kx, k_squar);
          Node conclusion = nm->mkNode(Kind::GT, n, kx_plus_k_squar);
          Node lem = nm->mkNode(Kind::IMPLIES, assumption, conclusion);
          d_im.addPendingLemma(
          lem, InferenceId::ARITH_NL_POW2_EVEN_CASE_REFINE, nullptr, true);
    }
    // assymptotic pow2 lemmas: k > 2 means x > k => pow2(x) > kx + k 
    // assymptotic pow2 lemmas: k > 2 means x > k+2 => pow2(x) > kx + k^2
    else if (x > 2 && pow2x <= x*x*2)
    { 
      Node x_plus_two = nm->mkNode(Kind::ADD, valXConcrete, d_two);
      Node assumption = nm->mkNode(Kind::GT, n[0], x_plus_two);
      Node kx = nm->mkNode(Kind::MULT, valXConcrete, n[0]);
      Node k_squar = nm->mkNode(Kind::MULT, valXConcrete, valXConcrete);
      Node kx_plus_k_squar = nm->mkNode(Kind::ADD, kx, k_squar);
      Node conclusion = nm->mkNode(Kind::GT, n, kx_plus_k_squar);
      Node lem = nm->mkNode(Kind::IMPLIES, assumption, conclusion);
      d_im.addPendingLemma(
      lem, InferenceId::ARITH_NL_POW2_EVEN_CASE_REFINE, nullptr, true);
    }


    // even pow2 lemma: x > 0 -> (pow2(x) - 1) mod 2 = 1
    if (x > 0 && (pow2x - Integer(1)).modByPow2(1) != 1)
    {
      Node assumption = nm->mkNode(Kind::GT, n[0], d_zero);
      Node power2_minus = nm->mkNode(Kind::SUB, n, d_one);
      Node mod_power2 = nm->mkNode(Kind::INTS_MODULUS, power2_minus, d_two);
      Node conclusion = nm->mkNode(Kind::EQUAL, mod_power2, d_one);
      Node lem = nm->mkNode(Kind::IMPLIES, assumption, conclusion);
      d_im.addPendingLemma(
      lem, InferenceId::ARITH_NL_POW2_EVEN_CASE_REFINE, nullptr, true);
    }

     for (uint64_t j = i + 1; j < size; j++)
    {
      Node m = d_pow2s[j];
      Node valPow2yAbstract = d_model.computeAbstractModelValue(m);
      Node valYConcrete = d_model.computeConcreteModelValue(m[0]);

      Integer y = valYConcrete.getConst<Rational>().getNumerator();
      Integer pow2y = valPow2yAbstract.getConst<Rational>().getNumerator();

      for (uint64_t k = j + 1; k < size; k++)
      {
        Node q = d_pow2s[k];
        Node valPow2zAbstract = d_model.computeAbstractModelValue(q);
        Node valZConcrete = d_model.computeConcreteModelValue(q[0]);

        Integer z = valZConcrete.getConst<Rational>().getNumerator();
        Integer pow2z = valPow2zAbstract.getConst<Rational>().getNumerator();

        // laws of exponents: 2^x * 2^y = 2^(x+y)
        if (x > 0 && y > 0 && x + y == z && pow2x * pow2y != pow2z)
        {
          Node x_plus_y = nm->mkNode(Kind::ADD,n[0], m[0]);
          Node assumption = nm->mkNode(Kind::EQUAL, x_plus_y, q[0]);
          Node n_mul_m = nm->mkNode(Kind::MULT, n, m);
          Node conclusion = nm->mkNode(Kind::EQUAL, n_mul_m, q);
          Node lem = nm->mkNode(Kind::IMPLIES, assumption, conclusion);
          d_im.addPendingLemma(
              lem, InferenceId::ARITH_NL_POW2_EXP_LAW_REFINE, nullptr, true);
        }
      }

    }
    // End of additional lemma schemas

    // this is the most naive model-based schema based on model values
    Node lem = valueBasedLemma(n);
    Trace("pow2-lemma") << "Pow2Solver::Lemma: " << lem << " ; VALUE_REFINE"
                        << std::endl;
    // send the value lemma
    d_im.addPendingLemma(
        lem, InferenceId::ARITH_NL_POW2_VALUE_REFINE, nullptr, true);
  }
}

Node Pow2Solver::valueBasedLemma(Node i)
{
  Assert(i.getKind() == POW2);
  Node x = i[0];

  Node valX = d_model.computeConcreteModelValue(x);

  NodeManager* nm = NodeManager::currentNM();
  Node valC = nm->mkNode(POW2, valX);
  valC = rewrite(valC);

  return nm->mkNode(IMPLIES, x.eqNode(valX), i.eqNode(valC));
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
