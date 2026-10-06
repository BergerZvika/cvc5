/******************************************************************************
 * Top contributors (to current version):
 *   Zvika Berger
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Constructive witness synthesis for triangular integer constraint systems:
 * propagate definitions, repair the residue by local search, and discharge the
 * problem outright when the resulting assignment is verified. Enabled by
 * --arith-witness-search.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__ARITH_WITNESS_SEARCH_H
#define CVC5__PREPROCESSING__PASSES__ARITH_WITNESS_SEARCH_H

#include <functional>
#include <unordered_map>
#include <vector>

#include "preprocessing/preprocessing_pass.h"
#include "util/integer.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * Try to SOLVE the problem in preprocessing by building a model, instead of
 * reasoning about why it is satisfiable.
 *
 * The target is the shape produced by termination/complexity analysers such as
 * LoAT: a long triangular chain of definitions
 *
 *     it2 = i2 + 1,  it493 = it3 - 2*it488*it13,  3*it552 = <degree-6 poly>, ...
 *
 * sitting on top of a handful of ROOT variables that carry all the real
 * constraints (`it13 >= 1`, `it1 = 2`, ...). Every variable but the roots is
 * FUNCTIONALLY DETERMINED, so a model is not something to search for in the
 * full space -- it is something to compute, once the roots are chosen.
 *
 * The pass therefore:
 *
 *  1. flattens the assertions into conjuncts and collects the integer
 *     variables;
 *  2. PROPAGATES: repeatedly finds an equality with exactly one unassigned
 *     variable occurring linearly, `c*v + Q = 0` with Q now ground, and sets
 *     `v := -Q/c` when c divides Q. Linearity is established by evaluating at
 *     v = 0, 1, 2 rather than by pattern matching, so it does not care how the
 *     equality is spelled;
 *  3. REPAIRS: whatever the propagation could not determine becomes a root.
 *     Roots start at the lower bound implied by the unit constraints on them,
 *     and are then hill-climbed against a penalty that measures, per conjunct,
 *     how far it is from holding -- so an unsatisfied `e > 0` pulls its roots
 *     in the direction that increases e. Each step re-propagates, so a change
 *     to a root moves the entire derived chain with it. Random kicks break
 *     plateaus;
 *  4. VERIFIES: if every conjunct is satisfied, the candidate is checked
 *     against the ORIGINAL assertions with substitution and the rewriter, not
 *     with the fast evaluator used during search. Only then are the assertions
 *     replaced by `true` and the values recorded as top-level substitutions.
 *
 * Because a positive answer is a verified model, the pass is one-sided and
 * cannot be unsound in the dangerous direction: failure changes nothing, and
 * success is checked by cvc5's own rewriter. It never derives `unsat`.
 *
 * This is a different mechanism from the vacuity route of
 * --arith-fermat-vacuity, which proves the hard equalities say nothing and
 * deletes them. Here they are kept and simply satisfied. The two reach
 * overlapping but not identical sets: this one also gets `twn05`, which no
 * amount of vacuity reasoning touches, because nothing in it is vacuous.
 */
class ArithWitnessSearch : public PreprocessingPass
{
 public:
  ArithWitnessSearch(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  using Assign = std::unordered_map<Node, Integer>;
  /**
   * Memo for one evaluation under one fixed assignment. These terms are DAGs
   * -- `let`-bound subterms are shared -- so an un-memoised recursion is
   * exponential in the sharing depth, not linear in the term size.
   */
  using Cache = std::unordered_map<TNode, Integer>;
  /** Conjuncts plus, per conjunct, its variables precomputed once. */
  struct Problem
  {
    std::vector<Node> d_conj;
    std::vector<std::vector<Node>> d_vars;
    /** indices of d_conj that are integer equalities */
    std::vector<size_t> d_eqs;
  };

  /** Evaluate an arithmetic term; false if it is outside the fragment. */
  bool evalTerm(TNode n, const Assign& a, Cache& ca, Integer& out) const;
  /** evalTerm without the memo lookup; call evalTerm, not this. */
  bool evalTermRec(TNode n, const Assign& a, Cache& ca, Integer& out) const;
  /**
   * Penalty of a conjunct: 0 when satisfied, otherwise a positive distance to
   * satisfaction. False if the conjunct is outside the fragment.
   */
  bool evalPenalty(TNode c, const Assign& a, Cache& ca, Integer& pen) const;
  /** Assign every equality that has exactly one unassigned linear variable. */
  void propagate(const Problem& p, Assign& a) const;
  /**
   * roots -> full assignment. The roots are replayed IN ORDER, propagating
   * after each one, which is what lets a root determine the variables further
   * down the chain instead of them being defaulted alongside it.
   */
  void complete(const Problem& p,
                const std::vector<Node>& vars,
                const std::vector<Node>& rootOrder,
                const Assign& roots,
                Assign& out) const;
  /** (#unsatisfied, total penalty); both zero means a candidate model. */
  bool costOf(const Problem& p,
              const Assign& a,
              size_t& nbad,
              Integer& total) const;

  /**
   * --arith-witness-enum: exhaustive small-width enumeration. Every variable
   * that occurs as the exponent of a power of two (the width k of a PBV
   * translation) is set to w = 1, 2, ..., and every other variable ranges over
   * [0, 2^w), exhaustively while the space fits the remaining budget and by
   * seeded random sampling for the last width that does not. A candidate that
   * the fast evaluator scores as a model is accepted only once `verified`
   * (the rewriter over the original assertions) agrees. At most `budget`
   * candidates are evaluated.
   */
  bool enumerateWidths(const Problem& p,
                       const std::vector<Node>& vars,
                       uint64_t budget,
                       const std::function<bool(const Assign&)>& verified,
                       Assign& found);

  struct Statistics
  {
    /** Problems discharged by a verified witness. */
    IntStat d_numSolved;
    /** Searches that ran and did not find one. */
    IntStat d_numFailed;
    /** Repair steps taken. */
    IntStat d_numSteps;
    /** Problems skipped as structurally unsuitable (not triangular). */
    IntStat d_numSkipped;
    /** Problems discharged by --arith-witness-enum. */
    IntStat d_numEnumSolved;
    Statistics(StatisticsRegistry& reg);
  };
  Statistics d_stats;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif
