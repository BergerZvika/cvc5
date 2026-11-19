/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Solver for parametric integer and (PIAND) constraints.
 */

#ifndef CVC5__THEORY__ARITH__NL__PIAND_SOLVER_H
#define CVC5__THEORY__ARITH__NL__PIAND_SOLVER_H

#include <map>
#include <set>
#include <string>
#include <vector>

#include "context/cdhashset.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/arith/nl/iand_utils.h"
#include "theory/theory_state.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

class ArithState;
class InferenceManager;

namespace nl {

class NlModel;

/** parametric Integer and solver class
 *
 */
class PIAndSolver : protected EnvObj
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  PIAndSolver(Env& env, InferenceManager& im, NlModel& model);
  ~PIAndSolver();

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
   * Returns a set of valid theory lemmas, based on simple facts about PIAND.
   *
   * Examples:
   *
   * 0 <= piand(k,x,y) < 2^k
   * piand(k,x,y) <= x
   * piand(k,x,y) <= y
   * x=y => piand(k,x,y)=x
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

  //-------------------------------------------- end lemma schemas
 private:
  // The inference manager that we push conflicts and lemmas to.
  InferenceManager& d_im;

  /** Reference to the non-linear model object */
  NlModel& d_model;

  /** commonly used terms */
  Node d_false;
  Node d_true;
  Node d_zero;
  Node d_one;
  Node d_two;

  IAndUtils d_iandUtils;
  /**
   * The lemma schemas selected by --piand-lemmas, with the aggregates `all`
   * and `complement-both` expanded.
   */
  std::set<std::string> d_lemmas;
  /** Is the --piand-lemmas schema `name` selected? */
  bool hasLemma(const char* name) const { return d_lemmas.count(name) > 0; }
  /** PIAND terms that have been given initial refinement lemmas */

  NodeSet d_initRefine;
  /**
   * PIAND terms created by the --piand-lemmas=complement split. They come back
   * in d_piands like any other term; recording them keeps the split from being
   * applied to its own output.
   */
  NodeSet d_complementIntroduced;
  /**
   * Pairs (as SEXPR nodes) already given the complement split by
   * --piand-lemmas=complement-existing.
   */
  NodeSet d_complementPairs;
  /**
   * The complement split restricted to pairs of PIAND terms that both already
   * occur in d_piands (--piand-lemmas=complement-existing); never creates a
   * new PIAND term.
   */
  void checkComplementExisting();
  /**
   * Relations between PIAND terms that all already occur in d_piands
   * (--piand-lemmas=subset-trans, subset-mono, pow2-idiom); never creates a
   * new PIAND term.
   */
  void checkSubsetExisting();
  /** Whether lem evaluates to false in the current abstract model. */
  bool modelFalsifies(const Node& lem);
  /**
   * a with purification skolems and reductions mod 2^k peeled off; congruent
   * to a mod 2^k, so it is what a PIAND at width k sees of a.
   */
  Node maskedForm(TNode a, TNode k);
  /**
   * The power term 2^j (EXP or POW2) if m is congruent to 2^j-1 mod 2^k
   * (--piand-lemmas=mask-sym), else null.
   */
  Node lowMaskPow(TNode m, TNode k);
  /** The result of alignedPows. */
  struct Alignment
  {
    /** a is 0 or a multiple of 2^k, so it masks to 0 at width k */
    bool d_zero = false;
    /** existing power terms 2^j (EXP or POW2) such that a is a multiple of
     * 2^j */
    std::set<Node> d_pows;
    bool empty() const { return !d_zero && d_pows.empty(); }
  };
  /**
   * Syntactic alignment of a, an argument of a PIAND at width k
   * (--piand-lemmas=align, align-id). Descends only through terms whose value
   * is eventually reduced mod 2^k: sums, products, ITE, mod 2^k, PIAND at the
   * same width and purification skolems. Under that reduction a summand that
   * is a multiple of 2^k counts as 0 for every 2^j: for j <= k it is a
   * multiple of 2^j, and for j > k a multiple of 2^j is itself 0 mod 2^k.
   */
  Alignment alignedPows(TNode a, TNode k, std::map<Node, Alignment>& memo);
  /** Whether c is (= 2^k 0), the guard of a purified mod 2^k. */
  bool isPow2kIsZero(TNode c, TNode k);
  /** The exponent of a power term 2^j (EXP or POW2). */
  static Node powExponent(TNode p);
  /**
   * Whether a is syntactically 2^k-1 (--piand-ones-rewrite): it rewrites to
   * 2^k-1 (with 2^k as EXP or POW2), or it is a mod by 2^k of -1 or of such a
   * term.
   */
  bool isOnes(TNode a, TNode k);
  /** all PIAND terms, for each bit-width */

  std::map<Node, std::vector<Node>> d_piands;

  /**
   * Value-based refinement lemma for i of the form (piand k x y). Returns:
   *   x = M(x) ^ y = M(y) =>
   *     (piand k x y) = rewrite((piand k M(x) M(y)))
   */
  Node valueBasedLemma(Node i);

  /**
   * Sum-based refinement lemma for i of the form ((_ piand k) x y). Returns:
   * i = 2^0*min(x[0],y[0])+...2^{k-1}*min(x[k-1],y[k-1])
   * where x[i] is x div i mod 2
   * and min is defined with an ite.
   */
  Node sumBasedLemma(Node i, Kind kind);
}; /* class PIAndSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__PIAND_SOLVER_H */
