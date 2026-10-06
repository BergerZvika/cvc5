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
 * Certification that a polynomial integer equality carrying a once-occurring
 * variable is vacuous, by deciding the residual congruence symbolically in the
 * Frobenius quotient ring rather than by enumerating residues. Enabled by
 * --arith-fermat-vacuity.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__ARITH_FERMAT_VACUITY_H
#define CVC5__PREPROCESSING__PASSES__ARITH_FERMAT_VACUITY_H

#include <map>
#include <vector>

#include "preprocessing/preprocessing_pass.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * Delete integer equalities that constrain nothing.
 *
 * An equality `c*v + Q = 0` in which the integer variable `v` occurs nowhere
 * else, and occurs here only as the linear monomial `c*v`, is satisfiable for
 * EVERY value of Q's variables exactly when |c| divides Q identically, i.e.
 *
 *     forall x in Z^n .  Q(x) = 0  (mod |c|)
 *
 * When that holds the assertion is equivalent to `true` and can be dropped
 * outright -- along with every nonlinear monomial in it. The motivating shape
 * is the LoAT/TPDB `size0*` family, where a degree-6..9 multivariate equality
 * carries a fresh variable with coefficient 3, and the residual congruence mod
 * 3 is a tautology by Fermat's little theorem. The apparent difficulty of
 * those benchmarks lies entirely in polynomials that say nothing.
 *
 * The question `does Q vanish identically mod m` is decided here SYMBOLICALLY.
 * For a prime p, two polynomials induce the same function on F_p^n iff they
 * agree after reducing coefficients mod p and collapsing every exponent e >= 1
 * to ((e-1) mod (p-1)) + 1 -- the Frobenius identity x^p = x read backwards.
 * Reduced polynomials have per-variable degree < p, and there are exactly as
 * many of them as there are functions F_p^n -> F_p, so the reduced form is a
 * NORMAL form: Q vanishes identically iff its reduction is the zero
 * polynomial. For composite m the test is run on each prime factor and
 * combined by the CRT, which needs m squarefree; a non-squarefree m is
 * declined rather than guessed at.
 *
 * Deciding it this way is what keeps the cost flat. The obvious alternative --
 * evaluating Q at all m^n residue tuples -- is exponential in the number of
 * variables and so has to be capped, and such a cap bites here: residual
 * polynomials in this family reach 10 distinct variables. Reduction to normal
 * form costs one traversal of Q and is independent of the variable count
 * altogether; the only budget is a cap on intermediate monomials, which guards
 * term blow-up from expanding a nested product, not the arity of the problem.
 *
 * Subterms that are not polynomial in integer variables -- an `exp` term with
 * a symbolic exponent, an uninterpreted application -- are treated as opaque
 * integer atoms, i.e. as further universally quantified variables. That is
 * conservative in the safe direction: it can only make the test decline, never
 * accept a Q that does not vanish.
 *
 * `v` is left with a witness in the top-level substitution map, `v := -Q div
 * c`, which is exact precisely because the divisibility was certified. So the
 * pass preserves models as well as satisfiability.
 */
class ArithFermatVacuity : public PreprocessingPass
{
 public:
  ArithFermatVacuity(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /** One sweep over the assertions; returns true if it changed anything. */
  bool sweep(AssertionPipeline* ap);
  /**
   * Does `q` vanish modulo `m` at every integer assignment? Sound but
   * incomplete: false means "not certified", not "does not vanish".
   */
  bool certifyVanishes(TNode q, const Integer& m);
  struct Statistics
  {
    /** Assertions certified vacuous and deleted. */
    IntStat d_numVacuous;
    /** Certification attempts that the normal form refused. */
    IntStat d_numDeclined;
    Statistics(StatisticsRegistry& reg);
  };
  Statistics d_stats;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif
