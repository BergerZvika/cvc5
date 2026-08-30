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
 * PBV-to-int translation.  Selected by --pbv-to-int-reduce-mods=MODE.
 *
 * ===========================================================================
 * MODES
 * ===========================================================================
 *
 *   none    do nothing (default)
 *   base    cases 1-5 below            -- the original set
 *   cav26   groups A and B below       -- adapted from the parabit rule set
 *   all     both
 *
 * The split exists so the two families can be benchmarked against each other.
 * They differ in kind, not just in coverage: every base rule strips an inner
 * mod that a surviving outer mod already subsumes, so the range information
 * the arithmetic solver uses is preserved.  The cav26 rules delete an outer
 * mod on the strength of a computed bound, which can remove the last mod
 * carrying a term's range.  That is a real trade -- a smaller formula against
 * a weaker purification bound -- and is why the two are separable.
 *
 * ===========================================================================
 * THE CASES  (mode: base)
 * ===========================================================================
 *
 * Write M(x, e) for `x mod 2^e` and P(e) for `2^e`.  Every rewrite below is
 * applied only when its side condition is *entailed* by the facts harvested
 * from the translated assertions; an unknown answer leaves the term alone.
 *
 * Case 1 - nested mod absorption
 *     M(M(x, m), k)  ->  M(x, k)                        when k <= m
 *   The inner mod only clears bits at or above m, all of which the outer mod
 *   clears anyway.  This is the dominant pattern: it is what an extract of an
 *   arithmetic PBV term translates to.
 *
 * Case 2 - vacuous outer mod
 *     M(M(x, m), k)  ->  M(x, m)                        when m <= k
 *   The inner mod already forces the value below 2^m <= 2^k, so the outer mod
 *   is the identity.  Complements case 1; together they handle a nested pair
 *   whenever the two widths are comparable in either direction.
 *
 * Case 3 - distribution through +, -, unary -, *
 *     M(f(.., M(a, m), ..), k)  ->  M(f(.., a, ..), k)  when k <= m
 *   for f in {ADD, SUB, NEG, MULT}.  Sound because these operators commute
 *   with reduction mod 2^k.  Applied at any depth.  This generalizes the
 *   existing PIntBlaster::rmModIfRedundant, which requires m and k to be
 *   *syntactically identical* and so never fires when the widths differ.
 *
 * Case 4 - distribution through ITE branches
 *     M(ite(c, M(a, m1), M(b, m2)), k)  ->  M(ite(c, a, b), k)
 *                                             when k <= m1 and k <= m2
 *   The condition c is never touched: stripping a mod inside a comparison
 *   would change its truth value.
 *
 * Case 5 - mod through a pow2 division (the extract shape)
 *     M(M(x, m) div P(j), w)  ->  M(x div P(j), w)      when j + w <= m
 *   Bits [j+w-1 : j] of `x mod 2^m` coincide with those of x as long as the
 *   window lies strictly below bit m.  Note the side condition is on j + w,
 *   not on w alone.
 *
 * Cases 6, 7 and 8 are DISABLED.
 *   6/7 relied on isPow2 recognizing a folded numeral (2, 4, 8, ...) as a
 *       power of two, which it no longer does.
 *   8   deleted a mod outright on an already-bounded term.  Unlike 1-5 it
 *       leaves no surviving mod to carry the range, so the arithmetic solver
 *       loses the purification bound it had been using.  Only sub-case 8a
 *       survives, and only because it IS case 2 (a nested mod remains).
 *
 * ===========================================================================
 * GROUP A - width bounds  (mode: cav26)
 * ===========================================================================
 *
 * Everything here is carried by one function, widthOf(t), which returns a
 * width expression `w` with `0 <= t < 2^w` entailed, or null.  An enclosing
 * `M(t, k)` is then the identity whenever `w <= k`.  The rules of the parabit
 * set fall out as the cases of that function:
 *
 *   widthOf(M(y, m))            = m                    [parabit 32]
 *   widthOf(c), c a numeral     = min e with 2^e > c   [parabit 15]
 *   widthOf(piand(u, _, _))     = u                    [parabit 60]
 *   widthOf(a + b)              = 1 + max(wa, wb)      [parabit 20]
 *   widthOf(a * b)              = wa + wb              [parabit 25]
 *   widthOf(a * b), wb = 1      = wa                   [parabit 26, 27]
 *   widthOf(a * 2^e)            = wa + ub(e)           [parabit 34]
 *   widthOf(a div d), d > 0     = wa                   [parabit 30]
 *   widthOf(a + b - piand)      = u                    [parabit 61]
 *   widthOf(a + b - 2*piand)    = u                    [parabit 62]
 *
 * A non-null result also certifies `t >= 0`; the sum and product cases depend
 * on that and would be unsound without it.
 *
 * The `max` in the sum case is not expressible as a term, so the two widths
 * are compared with the fact store and the case is declined when neither
 * direction is entailed.  The `ub(e)` in the shift case is the reason parabit
 * 34 is only partly covered: its side condition `s >= p + 2^q - 1` is
 * non-linear, and IntOrderFacts is a linear difference-bound store, so
 * valueUpperBound() answers only when the exponent's own width is a small
 * constant.  A symbolic shift-amount width is declined rather than guessed.
 *
 * ===========================================================================
 * GROUP B - rewrites not rooted at a mod  (mode: cav26)
 * ===========================================================================
 *
 * Case 11 - nested pow2 division                        [parabit 12]
 *     (a div 2^y) div 2^z  ->  a div 2^(y+z)            when y, z >= 0
 *   Composed with the `s^a * s^b -> s^(a+b)` merge in the arithmetic
 *   rewriter, this turns a NESTED exponential into a single one.  It is the
 *   integer-level counterpart of the PBV-level pbv-merge-lshr, which cannot
 *   fire once translation has happened.
 *
 * Case 12 - WITHDRAWN.  The parabit rules 63-65 strip a subsumed mod from an
 *   argument of a bitwise AND:
 *       piand(u, M(a, m), b)  ->  piand(u, a, b)        when u <= m
 *   That is valid for parabit's `and`, which is AND over unbounded integers.
 *   It is NOT valid here.  cvc5's PIAND carries an invariant that its two
 *   value arguments are already in [0, 2^u): postRewritePIAnd rewrites
 *   `piand(k, 2^k-1, y)` to `y` rather than to `y mod 2^k` (see the
 *   commented-out modulus in arith_rewriter.cpp), and several PIAND
 *   refinement lemmas are guarded by an explicit `x,y in [0,2^k)` assumption.
 *   Stripping the mod breaks that invariant.  Caught by
 *   sat25/mut/cade19_mutant/terms_size3-sat-bvshl-to-bvlshr/test-pbv1416.smt2,
 *   which flips unsat -> sat.  Restoring these three rules requires making
 *   PIAND total first, not changing this pass.
 *
 * Case 13 - bounded numerator over a wider divisor      [parabit 69]
 *     x div 2^j  ->  0                                  when x < 2^m, m <= j
 *
 * ===========================================================================
 * SIDE CONDITIONS
 * ===========================================================================
 *
 * All conditions reduce to "is `b - a` non-negative" over width expressions,
 * answered by IntOrderFacts (see int_order_facts.h), which harvests the
 * unconditional top-level integer atoms into a difference-bound store and
 * closes it transitively.  Facts are taken only from conjunctive top-level
 * positions and never from inside a binder; reduce() likewise does not enter
 * quantifier bodies.
 */

#include "preprocessing/passes/pbv_mod_reducer.h"

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "options/smt_options.h"
#include "util/integer.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

Pow2ModReducer::Pow2ModReducer(Env& env)
    : EnvObj(env), d_facts(env), d_base(false), d_cav26(false), d_numRemoved(0)
{
  d_two = nodeManager()->mkConstInt(Rational(2));
  d_zero = nodeManager()->mkConstInt(Rational(0));
  options::PbvReduceModsMode m = options().smt.pbvToIntReduceMods;
  d_base = (m == options::PbvReduceModsMode::BASE
            || m == options::PbvReduceModsMode::ALL);
  d_cav26 = (m == options::PbvReduceModsMode::CAV26
             || m == options::PbvReduceModsMode::ALL);
}

void Pow2ModReducer::bump(uint32_t caseNum)
{
  d_numRemoved++;
  d_caseCount[caseNum]++;
}

/* == pattern recognition =================================================== */

bool Pow2ModReducer::isPow2(TNode n, Node& e) const
{
  if (n.getKind() == Kind::POW2)
  {
    e = n[0];
    return true;
  }
  if (n.getKind() == Kind::EXP && n[0] == d_two)
  {
    e = n[1];
    return true;
  }
  // Folded numerals (2, 4, 8, ...) are deliberately NOT recognized: doing so
  // enabled the former cases 6 and 7, which are disabled.
  return false;
}

bool Pow2ModReducer::isMod(TNode n) const
{
  return n.getKind() == Kind::INTS_MODULUS
         || n.getKind() == Kind::INTS_MODULUS_TOTAL;
}

Node Pow2ModReducer::mkMod(TNode like, Node x, Node d) const
{
  return nodeManager()->mkNode(like.getKind(), x, d);
}

Node Pow2ModReducer::mkPow2Like(TNode like, Node e) const
{
  if (like.getKind() == Kind::POW2)
  {
    return nodeManager()->mkNode(Kind::POW2, e);
  }
  return nodeManager()->mkNode(Kind::EXP, d_two, e);
}

Node Pow2ModReducer::rebuild(TNode n, const std::vector<Node>& kids) const
{
  NodeBuilder nb(nodeManager(), n.getKind());
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    nb << n.getOperator();
  }
  for (const Node& c : kids)
  {
    nb << c;
  }
  return nb.constructNode();
}

/* == rewriting ============================================================= */

void Pow2ModReducer::harvest(const std::vector<Node>& assertions)
{
  d_facts.harvest(assertions);
  if (options().smt.pbvModVarWidths)
  {
    harvestVarWidths(assertions);
  }
}

Node Pow2ModReducer::reduce(Node n) { return reduceRec(n); }

Node Pow2ModReducer::reduceRec(TNode n)
{
  auto it = d_cache.find(n);
  if (it != d_cache.end()) return it->second;

  Node res;
  if (n.getNumChildren() == 0)
  {
    res = n;
  }
  else if (n.isClosure())
  {
    // Facts were harvested about free width atoms only, so they need not hold
    // for a quantified width. Leave bodies untouched.
    res = n;
  }
  else
  {
    std::vector<Node> kids;
    kids.reserve(n.getNumChildren());
    bool changed = false;
    for (const Node& c : n)
    {
      Node nc = reduceRec(c);
      changed = changed || (nc != c);
      kids.push_back(nc);
    }
    Node cur = changed ? rebuild(n, kids) : Node(n);
    // reduceTop applies at most one rule and returns, but the rules feed each
    // other: eliminating a shift guard exposes a mod, deleting that mod exposes
    // the nested division underneath, and only then can case 11 merge it. So
    // re-apply until the node stops changing. The bound is a safety net -- each
    // rule strictly removes an operator, so this terminates on its own.
    res = cur;
    for (unsigned iter = 0; iter < 16; ++iter)
    {
      Node nx = reduceTop(res);
      if (nx == res)
      {
        break;
      }
      res = nx;
    }
  }
  d_cache[n] = res;
  return res;
}

Node Pow2ModReducer::reduceTop(Node n)
{
  // Shift-guard elimination (--pbv-shift-guard-elim).
  //
  // bvlshrSym/bvshlSym wrap their division/multiplication in guards against a
  // degenerate `2^e = 0`, which can only be taken when e is negative:
  //
  //   ite(2^k = 0, ite(2^y = 0, 2^k-1, x div 2^y),
  //                ite(2^y = 0, 2^k-1, x div 2^y) mod 2^k)
  //
  // With e >= 0 entailed the test is false and the ite is its else branch.
  // The point is not the ite but what it hides: while the division sits under
  // two of them, the nested-division merge (a div 2^y) div 2^z -> a div 2^(y+z)
  // cannot match it and the surrounding mod cannot be dropped. parabit's
  // shr_def/shl_def carry no guard, which is why it merges these directly.
  if (options().smt.pbvShiftGuardElim && n.getKind() == Kind::ITE
      && n.getNumChildren() == 3 && n[0].getKind() == Kind::EQUAL
      && n[0].getNumChildren() == 2)
  {
    Node e;
    for (size_t i = 0; i < 2; ++i)
    {
      if (n[0][1 - i].isConst() && n[0][1 - i].getConst<Rational>().sgn() == 0
          && isPow2(n[0][i], e) && d_facts.nonNeg(e))
      {
        bump(20);
        return n[2];
      }
    }
  }
  // Group B fires on roots that are not mods, so it is tried first.
  if (d_cav26)
  {
    Node r = reduceNonMod(n);
    if (r != n)
    {
      return r;
    }
  }
  if (!isMod(n))
  {
    return n;
  }
  Node k;
  if (!isPow2(n[1], k))
  {
    return n;
  }
  Node x = n[0];

  // Case 2 / group A: the whole mod is the identity.
  if (boundedBy(x, k))
  {
    return x;
  }
  // Cases 1, 3, 4, 5: strip subsumed inner mods.
  if (d_base)
  {
    Node nx = stripInner(x, k);
    if (nx != x)
    {
      return mkMod(n, nx, n[1]);
    }
  }
  return n;
}

bool Pow2ModReducer::boundedBy(TNode x, TNode k)
{
  if (d_base)
  {
    Node m;
    // Case 2 only: x = y mod 2^m with m <= k, so x < 2^m <= 2^k already.
    //
    // The former case 8 (piand bound, numeral bound, harvested RANGE bound) is
    // deliberately NOT applied here: unlike cases 1-5 it deletes a mod without
    // any surviving mod to carry the bound, so the arithmetic solver loses the
    // purification range it had been relying on.  Group A is exactly that
    // trade made deliberately, which is why it sits behind its own mode.
    if (isMod(x) && isPow2(x[1], m) && d_facts.nonNeg(m) && d_facts.leq(m, k))
    {
      bump(2);
      return true;
    }
  }
  if (d_cav26)
  {
    // Group A: any term with a derivable width bound at or below k.
    Node w = widthOf(x);
    if (!w.isNull() && d_facts.leq(w, k))
    {
      bump(10);
      return true;
    }
    // Group A' (--pbv-mod-var-widths): the sum bound WITHOUT going through max.
    //
    // widthOf(a+b) is 1 + max(wa,wb), and `max` is not a term, so widthOf()
    // must compare wa and wb through the fact store and gives up when neither
    // direction is entailed. That is the common case: a goal states p < u and
    // r < u and says nothing relating p to r, so the bound is unavailable even
    // though EACH operand is strictly narrower than k.
    //
    // parabit's add_full_prec asks exactly that instead -- `(< q p)` and
    // `(< r p)` separately -- so it never needs max. Sum of two values each
    // below 2^(k-1) is below 2^k, so the enclosing mod is the identity.
    // Applied n-ary via a halving argument is NOT valid, so this fires only on
    // the binary case; a wider ADD is left alone.
    if (options().smt.pbvModVarWidths && x.getKind() == Kind::ADD
        && x.getNumChildren() == 2)
    {
      Node wa = widthOf(x[0]);
      Node wb = widthOf(x[1]);
      if (!wa.isNull() && !wb.isNull() && d_facts.lt(wa, k) && d_facts.lt(wb, k))
      {
        bump(14);
        return true;
      }
    }
  }
  return false;
}

/* == group A: width bounds ================================================= */


void Pow2ModReducer::harvestVarWidths(const std::vector<Node>& assertions)
{
  // The translation states a symbol's width as a RANGE atom rather than in the
  // term -- addRangeConstraints emits `0 <= x` and `x < 2^k` -- so widthOf()
  // sees nothing on a bare symbol. Recover k for x, which is the information
  // parabit keeps syntactically in `(bw k a)`.
  //
  // Two shapes are matched: the constraint as built, `(< x 2^k)`, and the form
  // it takes after arithmetic normalization, `(not (>= (+ x (* -1 2^k)) 0))`.
  // Conjunctions are descended, since the range pair arrives as one AND.
  // Anything else is skipped: a missing entry only leaves widthOf() answering
  // null exactly as before, so this costs completeness and never soundness.
  std::vector<TNode> work(assertions.begin(), assertions.end());
  std::unordered_set<TNode> seen;
  auto record = [&](TNode var, TNode e) {
    if (!var.isVar() || !var.getType().isInteger()) return;
    auto it = d_varWidth.find(var);
    if (it == d_varWidth.end() || d_facts.leq(e, it->second))
    {
      d_varWidth[var] = e;
    }
  };
  while (!work.empty())
  {
    TNode a = work.back();
    work.pop_back();
    if (!seen.insert(a).second) continue;
    if (a.getKind() == Kind::AND)
    {
      for (const Node& c : a) work.push_back(c);
      continue;
    }
    Node e;
    // `(< x 2^k)` as addRangeConstraints builds it.
    if (a.getKind() == Kind::LT && a.getNumChildren() == 2 && isPow2(a[1], e))
    {
      record(a[0], e);
      continue;
    }
    // `(not (>= (+ x (* -1 2^k)) 0))` after normalization.
    if (a.getKind() != Kind::NOT || a.getNumChildren() != 1) continue;
    TNode atom = a[0];
    if (atom.getKind() != Kind::GEQ || atom.getNumChildren() != 2) continue;
    if (!atom[1].isConst() || atom[1].getConst<Rational>().sgn() != 0) continue;
    TNode sum = atom[0];
    if (sum.getKind() != Kind::ADD || sum.getNumChildren() != 2) continue;
    for (size_t i = 0; i < 2; ++i)
    {
      TNode negPow = sum[i];
      if (negPow.getKind() != Kind::MULT || negPow.getNumChildren() != 2) continue;
      if (!negPow[0].isConst()
          || negPow[0].getConst<Rational>() != Rational(-1))
      {
        continue;
      }
      if (!isPow2(negPow[1], e)) continue;
      record(sum[1 - i], e);
      break;
    }
  }
}

Node Pow2ModReducer::widthOf(TNode x)
{
  auto it = d_widthCache.find(x);
  if (it != d_widthCache.end())
  {
    return it->second;
  }
  Node res = widthOfCompute(x);
  d_widthCache[x] = res;
  return res;
}

Node Pow2ModReducer::widthOfCompute(TNode x)
{
  NodeManager* nm = nodeManager();

  // A bare symbol carries no width in the term; the translation put it in a
  // RANGE atom instead (--pbv-mod-var-widths).
  if (x.isVar())
  {
    auto vit = d_varWidth.find(x);
    if (vit != d_varWidth.end())
    {
      return vit->second;
    }
  }

  // x = y mod 2^m  ->  m.  Requires m >= 0, else 2^m is not an integer and the
  // Euclidean remainder says nothing.
  {
    Node m;
    if (isMod(x) && isPow2(x[1], m) && d_facts.nonNeg(m))
    {
      return m;
    }
  }

  // A non-negative numeral c is below 2^e for the least e with 2^e > c.
  if (x.isConst() && x.getType().isInteger())
  {
    Rational r = x.getConst<Rational>();
    if (r.sgn() < 0 || !r.isIntegral())
    {
      return Node::null();
    }
    Integer v = r.getNumerator();
    uint32_t e = 0;
    for (Integer bound(1); bound <= v; bound = bound * Integer(2))
    {
      ++e;
    }
    return nm->mkConstInt(Rational(e));
  }

  // piand(u, _, _) is in [0, 2^u) by definition.
  if (x.getKind() == Kind::PIAND && x.getNumChildren() == 3
      && d_facts.nonNeg(x[0]))
  {
    return x[0];
  }

  // a + b < 2^(1 + max(wa, wb)).  `max` is not a term, so the two widths are
  // compared through the fact store; decline when neither direction is known.
  if (x.getKind() == Kind::ADD && x.getNumChildren() == 2)
  {
    Node wa = widthOf(x[0]);
    if (wa.isNull()) return Node::null();
    Node wb = widthOf(x[1]);
    if (wb.isNull()) return Node::null();
    Node hi;
    if (d_facts.leq(wb, wa))
    {
      hi = wa;
    }
    else if (d_facts.leq(wa, wb))
    {
      hi = wb;
    }
    else
    {
      return Node::null();
    }
    return rewrite(nm->mkNode(Kind::ADD, hi, nm->mkConstInt(Rational(1))));
  }

  if ((x.getKind() == Kind::MULT || x.getKind() == Kind::NONLINEAR_MULT)
      && x.getNumChildren() == 2)
  {
    // a * 2^e  ->  wa + ub(e).  This is the left-shift shape; ub(e) is a
    // constant or nothing at all (see valueUpperBound).
    for (uint32_t i = 0; i < 2; ++i)
    {
      Node e;
      if (!isPow2(x[i], e))
      {
        continue;
      }
      Node wo = widthOf(x[1 - i]);
      if (wo.isNull())
      {
        continue;
      }
      Node ub = valueUpperBound(e);
      if (!ub.isNull())
      {
        return rewrite(nm->mkNode(Kind::ADD, wo, ub));
      }
    }
    Node wa = widthOf(x[0]);
    if (wa.isNull()) return Node::null();
    Node wb = widthOf(x[1]);
    if (wb.isNull()) return Node::null();
    // A single-bit factor is 0 or 1, so the product is 0 or the other factor
    // and no extra bit is needed.
    if (wb.isConst() && wb.getConst<Rational>().isOne())
    {
      return wa;
    }
    if (wa.isConst() && wa.getConst<Rational>().isOne())
    {
      return wb;
    }
    return rewrite(nm->mkNode(Kind::ADD, wa, wb));
  }

  // Division by a positive divisor only shrinks a non-negative numerator.
  // A non-positive divisor is declined: INTS_DIVISION_TOTAL by 0 is 0, but a
  // negative divisor can make the quotient negative.
  if (x.getKind() == Kind::INTS_DIVISION
      || x.getKind() == Kind::INTS_DIVISION_TOTAL)
  {
    Node e;
    bool posDivisor =
        isPow2(x[1], e)
            ? d_facts.nonNeg(e)
            : (x[1].isConst() && x[1].getConst<Rational>().sgn() > 0);
    return posDivisor ? widthOf(x[0]) : Node::null();
  }

  // The or/xor encodings emitted by PIntBlaster:
  //     a | b  =  a + b - piand(u, a, b)
  //     a ^ b  =  a + b - 2 * piand(u, a, b)
  // Both are below 2^u provided a and b are, so the operands' own widths must
  // be checked -- the piand width alone does not bound the sum.
  if (x.getKind() == Kind::SUB && x.getNumChildren() == 2
      && x[0].getKind() == Kind::ADD && x[0].getNumChildren() == 2)
  {
    Node pi = x[1];
    if ((pi.getKind() == Kind::MULT || pi.getKind() == Kind::NONLINEAR_MULT)
        && pi.getNumChildren() == 2 && pi[0] == d_two)
    {
      pi = pi[1];
    }
    if (pi.getKind() == Kind::PIAND && pi.getNumChildren() == 3
        && pi[1] == x[0][0] && pi[2] == x[0][1] && d_facts.nonNeg(pi[0]))
    {
      Node wa = widthOf(x[0][0]);
      Node wb = widthOf(x[0][1]);
      if (!wa.isNull() && !wb.isNull() && d_facts.leq(wa, pi[0])
          && d_facts.leq(wb, pi[0]))
      {
        return pi[0];
      }
    }
  }

  return Node::null();
}

Node Pow2ModReducer::valueUpperBound(TNode e)
{
  if (e.isConst() && e.getType().isInteger())
  {
    Rational r = e.getConst<Rational>();
    if (r.sgn() >= 0 && r.isIntegral())
    {
      return e;
    }
    return Node::null();
  }
  // e < 2^we, so e <= 2^we - 1.  Only usable as a term when we is a constant:
  // the bound is exponential in we, and the fact store is linear.
  Node we = widthOf(e);
  if (we.isNull() || !we.isConst())
  {
    return Node::null();
  }
  Rational r = we.getConst<Rational>();
  if (r.sgn() < 0 || !r.isIntegral() || !r.getNumerator().fitsUnsignedInt())
  {
    return Node::null();
  }
  uint32_t q = r.getNumerator().getUnsignedInt();
  // Beyond a small q the bound is useless anyway (a shift by 2^32 - 1 is not
  // a width any benchmark asserts) and the numeral gets large.
  if (q > 16)
  {
    return Node::null();
  }
  return nodeManager()->mkConstInt(
      Rational(Integer(2).pow(q) - Integer(1)));
}

/* == group B: rewrites not rooted at a mod ================================= */

Node Pow2ModReducer::reduceNonMod(Node n)
{
  NodeManager* nm = nodeManager();
  Kind k = n.getKind();

  if (k == Kind::INTS_DIVISION || k == Kind::INTS_DIVISION_TOTAL)
  {
    // Case 11: (a div 2^y) div 2^z -> a div 2^(y+z).  Both divisors are >= 1
    // once y, z >= 0, so this is the ordinary floor-division identity and
    // holds for a negative numerator too.
    Node z;
    if (isPow2(n[1], z) && d_facts.nonNeg(z)
        && (n[0].getKind() == Kind::INTS_DIVISION
            || n[0].getKind() == Kind::INTS_DIVISION_TOTAL))
    {
      Node y;
      if (isPow2(n[0][1], y) && d_facts.nonNeg(y))
      {
        bump(11);
        Node sum = rewrite(nm->mkNode(Kind::ADD, y, z));
        return nm->mkNode(k, n[0][0], mkPow2Like(n[1], sum));
      }
    }
    // Case 13: a bounded numerator over a divisor at least as wide.
    Node j;
    if (isPow2(n[1], j))
    {
      Node m = widthOf(n[0]);
      if (!m.isNull() && d_facts.leq(m, j))
      {
        bump(13);
        return d_zero;
      }
    }
    return n;
  }

  // Case 12 (parabit 63-65) is NOT implemented -- see the file header.

  return n;
}

Node Pow2ModReducer::stripInner(TNode x, TNode k)
{
  Kind kk = x.getKind();

  // Case 1: (y mod 2^m) under an enclosing mod 2^k with k <= m.
  if (isMod(x))
  {
    Node m;
    if (isPow2(x[1], m) && d_facts.leq(k, m))
    {
      bump(1);
      return stripInner(x[0], k);
    }
    return x;
  }

  // Case 3: mod distributes over these.
  if (kk == Kind::ADD || kk == Kind::SUB || kk == Kind::NEG
      || kk == Kind::MULT || kk == Kind::NONLINEAR_MULT)
  {
    std::vector<Node> kids;
    kids.reserve(x.getNumChildren());
    bool changed = false;
    for (const Node& c : x)
    {
      Node nc = stripInner(c, k);
      changed = changed || (nc != c);
      kids.push_back(nc);
    }
    return changed ? rebuild(x, kids) : Node(x);
  }

  // Case 4: ITE branches only; the condition is left alone.
  if (kk == Kind::ITE && x.getNumChildren() == 3
      && x.getType().isInteger())
  {
    Node t = stripInner(x[1], k);
    Node e = stripInner(x[2], k);
    if (t != x[1] || e != x[2])
    {
      return nodeManager()->mkNode(Kind::ITE, x[0], t, e);
    }
    return x;
  }

  // Case 5: (y mod 2^m) div 2^j, window [j+k-1 : j] must sit below m.
  if ((kk == Kind::INTS_DIVISION || kk == Kind::INTS_DIVISION_TOTAL))
  {
    Node j;
    if (isPow2(x[1], j) && isMod(x[0]))
    {
      Node m;
      Node need = nodeManager()->mkNode(Kind::ADD, j, Node(k));
      if (isPow2(x[0][1], m) && d_facts.leq(need, m))
      {
        bump(5);
        Node inner = stripInner(x[0][0], need);
        return nodeManager()->mkNode(kk, inner, x[1]);
      }
    }
    return x;
  }

  // Anything else (division by a non-pow2, piand, UF application, EXP
  // exponent, comparison) does not commute with mod: stop here.
  return x;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
