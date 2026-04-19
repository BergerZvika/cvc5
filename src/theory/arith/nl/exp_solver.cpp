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

void ExpSolver::checkInitialRefine() {}

void ExpSolver::sortExpsBasedOnModel() {}

void ExpSolver::checkFullRefine() {}

Node ExpSolver::valueBasedLemma(Node i) {}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
