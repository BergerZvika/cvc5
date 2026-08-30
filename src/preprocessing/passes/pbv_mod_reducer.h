/******************************************************************************
 * Top contributors (to current version):
 *   Zvika Berger
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Redundant `mod 2^k` elimination for the NIA formula produced by the
 * PBV-to-int translation.  Enabled by --pbv-to-int-reduce-mods.
 */

#ifndef CVC5__PREPROCESSING__PASSES__PBV_MOD_REDUCER_H
#define CVC5__PREPROCESSING__PASSES__PBV_MOD_REDUCER_H

#include <map>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "preprocessing/passes/int_order_facts.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * Post-pass over the integer (NIA) formula produced by PIntBlaster.
 *
 * The translation applies one `mod 2^w` per PBV operator, so a PBV term whose
 * value is consumed at a narrower width picks up a chain of nested mods:
 *
 *     pextract (pbvadd a b) (k-1) 0   ==>   ((a + b) mod 2^m) mod 2^k
 *
 * Every surviving mod costs a purification skolem, two guard lemmas and a
 * nonlinear `q * 2^w` monomial in the arithmetic solver.  When the widths are
 * ordered (`k <= m`) the inner mod is redundant and can be deleted outright.
 *
 * The ordering facts needed to discharge the side conditions are already
 * present in the translated assertions: the ADM constraints emitted by
 * PIntBlaster include `i < kappa(t)` for every extract and `kappa > 0` for
 * every PBV variable, and the user's own width constraints (`(< t q)`, ...)
 * translate to plain integer atoms.  They are collected by IntOrderFacts.
 *
 * Usage:  harvest() over the full assertion list first, then reduce() each
 * assertion.  reduce() does not descend into quantifier bodies, so a bound
 * width variable can never be conflated with a free one of the same name.
 */
class Pow2ModReducer : protected EnvObj
{
 public:
  Pow2ModReducer(Env& env);

  /** Collect width-ordering facts from every assertion. Call before reduce(). */
  void harvest(const std::vector<Node>& assertions);

  /** Scan the assertions for `x < 2^p` range atoms and record p for x. */
  void harvestVarWidths(const std::vector<Node>& assertions);

  /** Rewrite n, deleting redundant `mod 2^k` subterms. */
  Node reduce(Node n);

  /** Number of rewrites applied so far (mods deleted, plus the group-B
   * rewrites, each of which also deletes a mod or a division). */
  uint64_t numRemoved() const { return d_numRemoved; }
  /** Per-case counters, indexed by the case numbers in the .cpp header. */
  const std::map<uint32_t, uint64_t>& caseCounts() const { return d_caseCount; }

 private:
  /* -- pattern recognition ------------------------------------------------ */

  /**
   * Recognize a power of two in any form PIntBlaster may emit:
   *   (** 2 e)      default EXP encoding
   *   (int.pow2 e)  --pbv-to-int-use-pow2
   * Folded numerals are NOT recognized (that enabled cases 6/7, now disabled).
   * On success sets `e` to the exponent and returns true.
   */
  bool isPow2(TNode n, Node& e) const;
  /** True for INTS_MODULUS / INTS_MODULUS_TOTAL. */
  bool isMod(TNode n) const;
  /** Build `x mod d`, preserving the modulus kind of `like`. */
  Node mkMod(TNode like, Node x, Node d) const;
  /** Build `2^e` in the same encoding (POW2 vs `(** 2 e)`) as `like`. */
  Node mkPow2Like(TNode like, Node e) const;
  /** Rebuild n with new children, preserving a parameterized operator. */
  Node rebuild(TNode n, const std::vector<Node>& kids) const;

  /* -- rewriting ---------------------------------------------------------- */

  Node reduceRec(TNode n);
  /** Apply the top-level cases to an already-rewritten node. */
  Node reduceTop(Node n);
  /**
   * Strip mods that are subsumed by an enclosing `mod 2^k`.
   * Cases 1, 3, 4, 5 - see the .cpp for the full list.
   */
  Node stripInner(TNode x, TNode k);
  /** Is `0 <= x < 2^k` entailed, making an enclosing `mod 2^k` vacuous? */
  bool boundedBy(TNode x, TNode k);

  /* -- cav26 group ---------------------------------------------------------
   *
   * Group A is carried entirely by widthOf(); group B by reduceNonMod().
   * Both are inert unless d_cav26.
   */

  /**
   * Symbolic width bound.  Returns a width expression `w` for which
   * `0 <= x < 2^w` is entailed, or a null Node when no bound is derivable.
   *
   * A non-null result therefore also certifies `x >= 0`, which the ADD and
   * MULT cases rely on.  Memoized in d_widthCache; the recursion is over a
   * DAG and cannot cycle.
   */
  Node widthOf(TNode x);
  /** Uncached body of widthOf(). */
  Node widthOfCompute(TNode x);
  /**
   * A constant `c` with `e <= c`, or null.  Used for the shift-amount bound of
   * rule 34, which needs `2^q - 1` as an actual numeral: the side condition is
   * non-linear and IntOrderFacts is a linear difference-bound store, so a
   * symbolic `q` is declined rather than approximated.
   */
  Node valueUpperBound(TNode e);
  /** Group B: rewrites whose root is not a mod (rules 12, 63-65, 69). */
  Node reduceNonMod(Node n);

  void bump(uint32_t caseNum);

  /** Entailment oracle over the width expressions. */
  IntOrderFacts d_facts;

  std::unordered_map<Node, Node> d_cache;
  /** x -> width bound, or a null Node meaning "no bound derivable". */
  std::unordered_map<Node, Node> d_widthCache;
  /**
   * Width of a bare symbol, read off the RANGE constraints (`x < 2^p`) that the
   * translation emits instead of keeping the width inside the term. Populated
   * only under --pbv-mod-var-widths; see harvestVarWidths.
   */
  std::unordered_map<Node, Node> d_varWidth;

  /** Run the original cases 1-5 (modes base, all). */
  bool d_base;
  /** Run the cav26 groups A and B (modes cav26, all). */
  bool d_cav26;

  uint64_t d_numRemoved;
  std::map<uint32_t, uint64_t> d_caseCount;
  Node d_two;
  Node d_zero;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__PBV_MOD_REDUCER_H */
