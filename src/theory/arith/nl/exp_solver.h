/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Solver for exponent constraints.
 */

#ifndef CVC5__THEORY__ARITH__NL__EXP_SOLVER_H
#define CVC5__THEORY__ARITH__NL__EXP_SOLVER_H

#include <utility>
#include <vector>

#include "context/cdhashset.h"
#include <map>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/theory_state.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

class InferenceManager;

namespace nl {

class NlModel;

/** exp solver class
 *
 */
class ExpSolver : protected EnvObj
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  ExpSolver(Env& env,
            TheoryState& state,
            InferenceManager& im,
            NlModel& model);
  ~ExpSolver();

  /** init last call
   *
   * This is called at the beginning of last call effort check, where
   * xts is the set of extended function terms that are active in
   * the current context.
   */
  void initLastCall(const std::vector<Node>& xts);
  //-------------------------------------------- lemma schemas
  /** check initial refine
   *
   * Returns a set of valid theory lemmas, based on simple facts about exp.
   *
   * Examples
   *
   * y>=0 --> y < exp(x y)
   *
   * This should be a heuristic incomplete check that only introduces a
   * small number of new terms in the lemmas it returns.
   */
  void checkInitialRefine();
  /** check full refine
   *
   * This should be a complete check that returns at least one lemma to
   * rule out the current model.
   */
  void checkFullRefine();

  /** sort d_exp according to their values in the current model */
  // void sortExpsBasedOnModel();

  //-------------------------------------------- end lemma schemas
  /**
   * SwInE phasing (Frohn & Giesl Sect. 5 / Alg. 3). Emit the level-b bound
   * -2^b <= t <= 2^b for the exponent of i, as an equivalence with a fresh
   * guard, and steer the SAT solver into the bounded (sat-phase) side.
   * Returns false if this term was already split at this level.
   */
  bool emitPhaseSplit(Node i);
  /**
   * True when the candidate model leaves the level-b bounded region, i.e. it
   * is an unsat-phase counterexample. In that case b is raised (the bound
   * doubles) and fresh splits are emitted; Alg. 3 discards such a model
   * WITHOUT computing refinement lemmas, so the caller skips refinement.
   * Returns false when the model respects the bound (a sat-phase model).
   */
  bool checkPhase();
  /** Ask the SAT solver to decide the literal for atom with polarity pol. */
  void preferAtom(Node atom, bool pol);

 private:
  // The inference manager that we push conflicts and lemmas to.
  /** reference to the theory state, for ensureLiteral in preferAtom */
  TheoryState& d_astate;
  //-------------------------------------------- phasing
  /** Current level b; the exponent bound is d_phaseBound = 2^b. */
  uint64_t d_phaseB;
  /** 2^d_phaseB, kept alongside b to avoid recomputing it. */
  Integer d_phaseBound;
  /** The guard Boolean for each (EXP term, level) pair, created on demand. */
  std::map<std::pair<Node, uint64_t>, Node> d_phaseGuards;
  /** Guards whose split lemma has already been emitted (user-context). */
  NodeSet d_phaseEmitted;
  //-------------------------------------------- end phasing
  InferenceManager& d_im;
  /** Reference to the non-linear model object */
  NlModel& d_model;
  /** commonly used terms */
  Node d_false;
  Node d_true;
  Node d_zero;
  Node d_one;
  Node d_two;
  Node d_negone;

  NodeSet d_initRefine;
  /** all exp terms
   * Cleared at each last call effort check.
   * */
  std::vector<Node> d_exps;

  /**
   * Value-based refinement lemma for i of the form (exp x y). Returns:
   *   x = M(x) /\ x>= 0 ---->
   *     (exp x y) = rewrite((exp M(x) M(y)))
   */
  Node valueBasedLemma(Node i);

  //-------------------------------------------- SwInE lemma families
  /**
   * Emit the exponent-composition lemma for the model-violating nested term n
   * in the full-refine loop: exp(exp(x,y),z) = exp(x, y*z).
   */
  void checkComposeRefine(Node n);

  /**
   * General monotonicity (`mon`, Frohn & Giesl Sect. 4.2.2), enabled by
   * --arith-exp-mon-general. Scans every pair of EXP terms and, for a pair the
   * candidate model orders but whose values violate the ordering, emits
   *
   *   2<=s1 /\ s1<=s2 /\ 0<=t1 /\ t1<=t2 /\ 1<=t2 /\ (s1<s2 \/ t1<t2)
   *     =>  exp(s1,t1) < exp(s2,t2)
   *
   * Unlike the inline pair lemmas of checkFullRefine this does not require the
   * two bases to be equal in the model, and it subsumes both of them.
   */
  void checkMonotonicityRefine();

  /**
   * Guarded same-base fusion, selected by --arith-exp-lemmas=fuse:
   *
   *   s1 = s2 /\ t1 >= 0 /\ t2 >= 0 => exp(s1,t1) * exp(s2,t2) = exp(s1,t1+t2)
   *
   * Valid here for every integer base because cvc5's EXP is SMT-LIB `**`,
   * which agrees with ordinary exponentiation on non-negative exponents --
   * unlike SwInE's EIA, whose s^|t| reading makes the unguarded rewrite
   * unsound. Emitted only when the fused term already exists in the problem
   * (or folds to a constant), so it introduces nothing into the term graph and
   * cannot diverge.
   */
  void checkFuseRefine();
  /**
   * Emit symmetry lemmas for the model-violating term n in the full-refine
   * loop, restricted to the lemmas whose antecedent holds in the model (so
   * they can actually rule out the current counterexample).
   */
  void checkSymmetryRefine(Node n, const Integer& model_t);
  /** Append bounding lemmas (bnd2,bnd3,bnd5) for exp(s,t) to conj. */
  /**
   * Bounding as a live refinement family (--arith-exp-bounding=refine|both):
   * the same bnd2/bnd3/bnd5 as addBoundingLemmas, but emitted one at a time
   * and only when the candidate model violates them, so that Bounding behaves
   * like an ordinary ComputeLemmas kind rather than a static axiom batch.
   */
  void addBoundingRefine(Node i,
                         const Integer& ms,
                         const Integer& mt,
                         const Integer& mv);

  void addBoundingLemmas(Node i, std::vector<Node>& conj);
  /** Emit the prime lemma for exp(s,t) given its model values, if any. */
  void checkPrimeLemma(Node n, const Integer& model_s, const Integer& expx);
  /** Emit the induction lemma relating same-base terms n and m, if any. */
  void checkInductionLemma(Node n,
                           Node m,
                           const Integer& model_s,
                           const Integer& model_t,
                           const Integer& model_sy,
                           const Integer& model_ty);
  /** Emit interpolation lemmas (ip2 upper / ip3 lower) for exp(s,t). */
  void checkInterpolationLemma(Node n,
                               const Integer& model_s,
                               const Integer& model_t,
                               const Integer& expx);
  /**
   * Points (c,d) where an upper interpolation lemma has been applied, used to
   * pick a nearest secant point for ip2. Persists across last-call checks.
   */
  std::vector<std::pair<Integer, Integer>> d_interpPoints;
  //-------------------------------------------- end SwInE lemma families
}; /* clas ExpSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__EXP_SOLVER_H */

