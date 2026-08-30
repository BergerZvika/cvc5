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
 * A conservative entailment oracle over the linear integer atoms of a
 * formula: harvest unconditional order facts, then answer `a <= b`.
 */

#ifndef CVC5__PREPROCESSING__PASSES__INT_ORDER_FACTS_H
#define CVC5__PREPROCESSING__PASSES__INT_ORDER_FACTS_H

#include <map>
#include <utility>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * Collects the unconditional linear order facts of an assertion list into a
 * difference-bound store, then answers entailment queries about integer
 * terms.  Used to discharge the side conditions of rewrites and lemmas that
 * are only sound under a known ordering (e.g. `k <= m` for a nested-mod
 * reduction, or `x <= y` for a power factorization).
 *
 * Every query is CONSERVATIVE: a `false` answer means "not entailed by the
 * harvested facts", never "false".  Callers must therefore treat false as
 * "do nothing".
 *
 * Facts are gathered only from conjunctive top-level positions (never from a
 * disjunct) and never from inside a binder, so a bound variable is never
 * confused with a free one of the same name.
 */
class IntOrderFacts : protected EnvObj
{
 public:
  IntOrderFacts(Env& env);

  /** Harvest order facts from every assertion. Call before any query. */
  void harvest(const std::vector<Node>& assertions);

  /** Is `a <= b` entailed? Memoized. */
  bool leq(TNode a, TNode b);
  /** Is `a < b` entailed (integers: `a + 1 <= b`)? */
  bool lt(TNode a, TNode b);
  /** Is `0 <= e` entailed? */
  bool nonNeg(TNode e);
  /** Is `e >= c` entailed, for an integer constant c? */
  bool geqConst(TNode e, const Rational& c);

  /**
   * Append every `y` for which a fact `y - x >= 1` was harvested, i.e. every
   * known strict upper bound term of x.  Used to recover RANGE bounds such as
   * `x < 2^m` that were recorded as difference constraints.
   */
  void strictUpperBoundsOf(TNode x, std::vector<Node>& out) const;

 private:
  /** A linear polynomial: sum of d_coeffs[atom]*atom, plus d_const. */
  struct Lin
  {
    std::map<Node, Rational> d_coeffs;
    Rational d_const;
  };

  Lin toLin(TNode n) const;
  static Lin linSub(const Lin& a, const Lin& b);
  /** Record the fact `d >= 0`. */
  void addGeq(const Lin& d);
  /** Walk a top-level assertion collecting unconditional atoms. */
  void collectFacts(TNode a, bool negated);
  /** Transitive closure over the difference-bound store. */
  void closeDiffs();
  /** Is `d >= 0` entailed by the harvested facts? */
  bool provNonNeg(const Lin& d) const;

  /** atom -> greatest known lower bound */
  std::map<Node, Rational> d_lb;
  /** atom -> least known upper bound */
  std::map<Node, Rational> d_ub;
  /** (x,y) -> greatest known c with x - y >= c */
  std::map<std::pair<Node, Node>, Rational> d_diff;
  /**
   * Facts with more than two variables, kept verbatim. The difference-bound
   * closure cannot represent them, but a query `d >= 0` still succeeds when
   * `d - f` is a non-negative constant for some stored fact `f >= 0`. That is
   * what lets a precondition like `p + r <= u` discharge a product bound.
   */
  std::vector<Lin> d_general;

  std::map<std::pair<Node, Node>, bool> d_leqCache;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__INT_ORDER_FACTS_H */
