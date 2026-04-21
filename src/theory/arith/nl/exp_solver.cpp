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

    Node lem = nm->mkAnd(conj);
    // x > 0 /\ y >= 0 -> (exp x y) > 0
    Node xgt0 = nm->mkNode(Kind::GT, i[0], d_zero);
    Node ygeq0 = nm->mkNode(Kind::GEQ, i[1], d_zero);
    Node nonegative = nm->mkNode(Kind::GT, i, d_zero);
    Node pos_assum = nm->mkNode(Kind::AND, xgt0, ygeq0);
    conj.push_back(nm->mkNode(Kind::IMPLIES, pos_assum, nonegative));

    // even: x mod 2 = 0 /\ y > 0 -> (exp x y) mod 2 = 0
    // Node xmod2 = nm->mkNode(Kind::INTS_MODULUS, i[0], d_two);
    // Node ygt0 = nm->mkNode(Kind::GT, i[1], d_zero);
    // Node mod2 = nm->mkNode(Kind::INTS_MODULUS, i, d_two);
    // Node even = nm->mkNode(Kind::EQUAL, mod2, d_zero);
    // Node even_assum = nm->mkNode(Kind::AND, xmod2, ygt0);
    // conj.push_back(nm->mkNode(Kind::IMPLIES, even_assum, even));

    Trace("exp-lemma") << "ExpSolver::Lemma: " << lem << " ; INIT_REFINE"
                        << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_EXP_INIT_REFINE);
  }
}


void ExpSolver::sortExpsBasedOnModel() {}

void ExpSolver::checkFullRefine() {}

Node ExpSolver::valueBasedLemma(Node i) {}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
