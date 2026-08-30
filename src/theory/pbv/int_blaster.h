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
 * Lazy translation pipeline (TRANS and CONV) for parametric bit-vectors.
 *
 * Implements Section 4.2 of the PBV paper:
 *
 *   TRANS(φ) = CONV(φ ∧ RANGE(φ) ∧ ADM(φ))
 *
 * CONV translates PBV terms to integer arithmetic:
 *   CONV(x)             = χ(x)                       [fresh Int variable]
 *   CONV(|t|)           = κ(t)                        [symbolic bit-width]
 *   CONV(to-pbv(k,t))   = CONV(t) mod pow2(k)
 *   CONV(t1 +^B t2)     = (CONV(t1)+CONV(t2)) mod pow2(κ(t1))
 *   CONV(t1 &^B t2)     = piand(κ(t1), CONV(t1), CONV(t2))
 *   [etc. — full table in Algorithm 3]
 *
 * κ(t) is the symbolic bit-width of t (BW function, Algorithm 2):
 *   κ(x)              = fresh Int variable  (d_kappaMap[x])
 *   κ(to-pbv(k,v))    = k
 *   κ(t[i:j])         = i - j + 1
 *   κ(ext(n,t))       = κ(t) + n
 *   κ(t1 ○ t2)        = κ(t1) + κ(t2)
 *   κ(ite(c,t2,t3))   = κ(t2)
 *   κ(◇(t1,...))      = κ(t1)   [all other PBV ops]
 *
 * RANGE(φ) adds: 0 ≤ χ(x) < pow2(κ(x)) for each free PBV variable x.
 * ADM(φ) adds:  κ(x) > 0, and κ(t1) = κ(t2) for equal-width operators.
 */

#include "cvc5_private.h"

#ifndef __CVC5__THEORY__PBV__INT_BLASTER__H
#define __CVC5__THEORY__PBV__INT_BLASTER__H

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdo.h"
#include "options/smt_options.h"
#include "proof/proof_generator.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"
#include "theory/arith/nl/iand_utils.h"

namespace cvc5::internal {

class PIntBlaster : protected EnvObj, public ProofGenerator
{
  using CDNodeMap = context::CDHashMap<Node, Node>;

 public:
  /**
   * Constructor.
   * @param env  the solver environment
   */
  PIntBlaster(Env& env);

  ~PIntBlaster();

  /**
   * Translate PBV formula n to integer arithmetic.
   * Implements TRANS(n) = CONV(n ∧ RANGE(n) ∧ ADM(n)).
   *
   * @param n        PBV formula to translate (must already be rewritten)
   * @param lemmas   output: range and admissibility lemmas added by RANGE/ADM
   * @param skolems  output: map from PBV variables x to INT_TO_PBV(κ(x),χ(x))
   * @return TrustNode for rewrite n → CONV(n), or null if n is unchanged
   */
  TrustNode trustedIntBlast(Node n,
                            std::vector<TrustNode>& lemmas,
                            std::map<Node, Node>& skolems);

  /**
   * Binarize n-ary PBV operators (ADD, MULT, AND, OR, XOR, CONCAT) into
   * left-associative binary trees before translation.
   */
  Node makeBinary(Node n);

  /** ProofGenerator interface. */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  std::string identify() const override;

  /**
   * Pre-scan one assertion for kappa-equivalence info (union-find +
   * explicit width). Idempotent. Call this for every assertion BEFORE the
   * first call to `trustedIntBlast`, so that the union-find has global
   * visibility before any kappa skolem is allocated.
   */
  void scanAssertion(Node n) { buildKappaUnionFind(n); }

  /** Look up χ(pbvVar) without creating one. Returns null if absent. */
  Node lookupChi(Node pbvVar) const;
  /** Look up κ(pbvVar) without creating one. Returns null if absent. */
  Node lookupKappa(Node pbvVar) const;

 protected:
  /**
   * CONV for a node whose children have already been translated (post-order).
   * Implements the operator-by-operator cases of Algorithm 3.
   */
  Node translateWithChildren(Node original,
                             const std::vector<Node>& translated_children,
                             std::vector<TrustNode>& lemmas);

  /**
   * CONV for leaf nodes: PBV variables → χ, integer constants/vars → identity,
   * CONST_PBV → integer value, function symbols → translated UF.
   */
  Node translateNoChildren(Node original,
                           std::vector<TrustNode>& lemmas,
                           std::map<Node, Node>& skolems);

  /**
   * Compute κ(t): symbolic bit-width expression for PBV term t (Algorithm 2).
   * For PBV variables, creates a fresh Int skolem stored in d_kappaMap.
   * For structural terms, returns an arithmetic expression over κ variables.
   * Results are memoized in d_kappaMap.
   */
  Node computeKappa(Node t);

  /** Build: mkNode(Kind::EXP, 2, k)  — symbolic 2^k with Int-sort argument. */
  Node mkPow2Sym(Node k);

  /** Build: n mod 2^k  = mkNode(modKind(), n, EXP(2, k)). */
  Node modPow2Sym(Node n, Node k);

  /**
   * The integer-modulus kind used throughout the translation: INTS_MODULUS_TOTAL
   * by default, or the partial INTS_MODULUS when --pbv-to-int-partial-mod is set.
   */
  Kind modKind() const;
  /** Build: mkNode(modKind(), n, d). */
  Node mkMod(Node n, Node d);

  /**
   * Unsigned-to-signed conversion with symbolic bit-width k (Algorithm 3).
   *   utsSym(k, x) = x - ite(x < pow2(k-1), 0, pow2(k))
   * Correct over the range [0, pow2(k)) established by RANGE constraints.
   */
  Node utsSym(Node k, Node x);

  /**
   * Match smt-switch AbstractPBVWalker::bvlshr(x, y) (default form):
   *   intTerm = x div pow2(y)
   *   inner   = ite(pow2(y) = 0, pow2(k) - 1, intTerm)
   *   result  = ite(pow2(k) = 0, inner, inner mod pow2(k))
   */
  Node bvlshrSym(Node x, Node y, Node k);

  /**
   * Get or create χ(pbvVar): fresh Int skolem for the integer value of the
   * free PBV variable pbvVar.  Stored in d_chiMap.
   */
  Node getOrCreateChi(Node pbvVar);

  /**
   * Get or create κ(pbvVar): one named Int constant per kappa-equivalence
   * class. The first class is `k`, then `k1`, `k2`, … . Multiple PBV
   * variables that the formula constrains to share a width all map to the
   * same node; no per-variable skolem is allocated.
   */
  Node getOrCreateKappa(Node pbvVar);

  /**
   * Pre-pass: walk n and build a union-find over PBV terms so that any two
   * terms that are operands of an equal-width operator (PBV_ADD, EQUAL,
   * ITE-over-PBV, …) share a kappa class. Also propagates through unary
   * width-preserving operators (PBV_NOT, PBV_NEG, PBV_AND-result, …) by
   * unioning their operand chains.
   */
  void buildKappaUnionFind(Node n);

  /** Union-find: find and (path-compressed) representative of `t`. */
  Node kappaFind(Node t);

  /** Union-find: merge classes of `a` and `b`. */
  void kappaUnion(Node a, Node b);

  /**
   * Reduce `t` to a representative PBV leaf whose kappa equals κ(t).
   * Recurses through width-preserving unary ops (PBV_NOT, PBV_NEG, ITE,
   * the two operands of binary equal-width ops, …) and returns the first
   * variable / CONST_PBV leaf reached. Returns Node::null() when κ(t) is
   * structural (concat, extract, extend, int_to_pbv) and has no single
   * variable witness.
   */
  Node kappaSource(Node t);

  /**
   * Emit RANGE(e) constraints as lemmas (Algorithm 4).
   * Traverses e and for each free PBV variable x emits:
   *   0 ≤ χ(x)  ∧  χ(x) < pow2(κ(x))
   */
  void addRangeConstraints(Node e, std::vector<TrustNode>& lemmas);

  /**
   * Emit ADM(e) constraints as lemmas (Algorithm 1).
   * For each free PBV variable x:    κ(x) > 0
   * For equal-width PBV binary ops:  κ(t1) = κ(t2)
   * For ITE over PBV:               κ(t2) = κ(t3)
   */
  void addAdmConstraints(Node e, std::vector<TrustNode>& lemmas);

 public:
  /**
   * The ADM(n) constraints emitted during translation, i.e. the local width
   * side conditions of each sub-term: equal operand widths for the
   * equal-width operators, matching branch widths for ITE, and positivity of
   * every free PBV variable's width. This is the shallow type-check query of
   * --pbv-type-check; it is a conjunction of linear integer constraints.
   */
  const std::vector<Node>& getAdmConstraints() const { return d_admConstraints; }
  /**
   * The Int constants standing for widths: one per kappa-equivalence class.
   * A constraint all of whose free symbols lie in this set is a constraint on
   * widths alone, which is what the deep type-check query keeps.
   */
  std::unordered_set<Node> getWidthSymbols() const;

 private:

  /**
   * Pre-pass before translation: walk every quantifier in n and, for each
   * bound PBV variable x, register a fresh bound Int variable in d_kappaMap
   * to play the role of κ(x). The bound kappa appears in the bound-variable
   * list of the rebuilt quantifier, alongside x_int; the runtype/runrange
   * guard for x is then attached as the antecedent (FORALL) or conjunct
   * (EXISTS) inside the quantifier's body.
   */
  void registerBoundKappas(Node n);

  /** Returns true if the translated type of any child of n differs from its
   *  original type. */
  bool childrenTypesChanged(Node n);

  /**
   * Reconstruct a node whose operator is not directly translated.
   * Children that were translated from PBV/BV to Int are cast back as needed.
   */
  Node reconstructNode(Node originalNode,
                       TypeNode resultType,
                       const std::vector<Node>& translated_children);

  /**
   * Cast n to type tn.
   *   Int → BV:  applies INT_TO_BV operator.
   *   BV  → Int: applies BITVECTOR_UBV_TO_INT.
   *   PBV → Int or Int → PBV: returns n unchanged (PBV nodes are handled
   *   explicitly in translateWithChildren; this path is a safe fallback).
   */
  Node castToType(Node n, TypeNode tn);

  /**
   * Translate a PBV/BV uninterpreted function symbol to an Int→Int function.
   */
  Node translateFunctionSymbol(Node bvUF, std::map<Node, Node>& skolems);

  /**
   * Post-walker over the translated formula: when we see
   *   (a + b) mod m, (a - b) mod m, or (a * b) mod m
   * strip any redundant inner `mod m` on a / b (or inside ITE branches).
   * Also folds 0*x → 0. Mirrors the smt-switch PostPBVWalker behaviour.
   */
  Node reduceRedundantMods(Node n);

  /**
   * Scan the translated formula for self-squaring patterns of the form
   *   (= x (mod (* x x) p))
   * (with p any term, typically `pow2(k)`) and emit the lemma
   *   (=> (= x (mod (* x x) p)) (<= x 1))
   * Reason: in any bit-vector of width n, the only solutions to
   * `s ≡ s² (mod 2^n)` are `s = 0` and `s = 1`. Mirrors smt-switch's
   * `PostPBVWalker::visit_term` rule.
   */
  void detectSelfSquaring(Node n, std::vector<TrustNode>& lemmas);

  /** If node = (e mod modValue) and removing the mod is safe, return e. */
  Node rmModIfRedundant(Node node, Node modValue);

  /**
   * Replace every `(pbvsize V)` subterm with `computeKappa(V)`. Used when
   * emitting admissibility constraints whose width arguments come from raw
   * (untranslated) PBV positions like the indices of pextract or the
   * extension amount of sign/zero-extend. Without this, `(pbvsize V)` leaks
   * into the post-translation formula as an untranslated UF.
   */
  Node normalizeWidthExpr(Node n);

 public:
  /** Public wrapper: map every `(pbvsize V)` in n to its kappa term. */
  Node toWidthTerm(Node n) { return normalizeWidthExpr(n); }

 private:

  // ---- caches (context-dependent) ----------------------------------------
  /** Memoization for makeBinary. */
  CDNodeMap d_binarizeCache;
  /** Main translation cache: original node → CONV(node). */
  CDNodeMap d_intblastCache;
  /** χ map: free PBV variable x → fresh Int skolem χ(x). */
  CDNodeMap d_chiMap;
  /** κ map: PBV term t → Int-sort expression for κ(t). */
  CDNodeMap d_kappaMap;
  /** κ union-find: PBV leaf → its parent leaf in the equivalence class. */
  std::unordered_map<Node, Node> d_kappaUnionFind;
  /** κ classes → allocated named Int constant (k, k1, k2, …). */
  std::unordered_map<Node, Node> d_kappaClassSkolem;
  /** ADM(n) constraints, recorded separately for --pbv-type-check. */
  std::vector<Node> d_admConstraints;
  /**
   * κ classes with a known explicit width expression. When a PBV variable
   * is constrained (via int_to_pbv K _) to have width K (some Int term in
   * the user's formula), we record K here and reuse it instead of
   * allocating a fresh skolem — so the kappa references K directly.
   */
  std::unordered_map<Node, Node> d_kappaClassExplicit;
  /** Counter for the next kappa-class name. */
  size_t d_kappaClassCount = 0;

  /**
   * Admissibility constraints generated inside a quantifier scope. Such
   * constraints reference the quantifier's bound integer kappa(s); emitting
   * them at the top level would let those bound variables escape and capture
   * a free skolem of the same name. Instead they are folded into the
   * quantifier's guard when the FORALL/EXISTS is rebuilt.
   */
  std::unordered_map<Node, std::vector<Node>> d_quantAdmConstraints;

  NodeManager* d_nm;

  /** Set of range/admissibility constraints already emitted (deduplication). */
  context::CDHashSet<Node> d_rangeAssertions;
  context::CDHashSet<Node> d_bitwiseAssertions;

  /** Useful integer constants. */
  Node d_zero;
  Node d_one;
  Node d_two;

  /** IAndUtils kept for potential bitwise fallback (compatibility). */
  theory::arith::nl::IAndUtils d_iandUtils;

  context::Context* d_context;
};

}  // namespace cvc5::internal

#endif /* __CVC5__THEORY__PBV__INT_BLASTER__H */
