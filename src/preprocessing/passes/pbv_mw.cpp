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
 * See pbv_mw.h.
 *
 * ===========================================================================
 * THE RULES
 * ===========================================================================
 *
 * The catalogue of both kinds of rule. The CONDITIONAL ones -- every rule
 * with a side condition -- are no longer gated by their family's --pbv-*
 * flag: they are selected by --learned-rewrite-rules, run in the
 * learned-rewrite-pbv pass, and their bodies are in learned_rewrite_pbv.cpp
 * (which lists them). The --pbv-* flags below gate only the unconditional
 * rules that remain here; the families that had none left (A/B, E, R, K)
 * have lost their flags.
 *
 * A/B: --learned-rewrite-rules=preprocess-mw.
 *
 * Write EXT for either pzero_extend or psign_extend, and w(t) for the
 * symbolic width of t.  Every rule's side condition is decided by
 * rewrite(a - b) == 0 over widths resolved through the alias map.
 *
 * A. ANNIHILATION AT AN EXTENSION            side condition: w(x) = i + 1
 *    A1  (pextract (pzero_extend n x) i 0)  ->  x
 *    A2  (pextract (psign_extend n x) i 0)  ->  x
 *    The low w(x) bits of an extension are exactly its source.
 *
 * B. PUSH A LOW EXTRACT THROUGH AN OPERATOR  side condition: w(x) = i + 1
 *    B1  (pextract (OP (EXT n x) y) i 0)  ->  (OP x (pextract y i 0))
 *    B2  (pextract (OP y (EXT n x)) i 0)  ->  (OP (pextract y i 0) x)
 *    for OP in {pbvor, pbvxor, pbvadd, pbvsub, pbvmul}.  Sound because the
 *    low i+1 bits of OP(a,b) depend only on the low i+1 bits of a and b.
 *    When both operands are extensions, B fires once and A collapses the rest.
 *
 *    pbvand is EXCLUDED: the RARE rule pbv-reverse-extract-and rewrites in the
 *    opposite direction and the pair would not terminate.
 *
 * C and D (shift-of-shift merge, nested extension merge) are NOT here: they
 * carry no width side condition, so they work as ordinary RARE rules and live
 * in the rewriter under --pbv-rw-mw (`pbv-merge-*`).
 *
 * REMOVED - kept for reference only:
 * C. SHIFT-OF-SHIFT MERGE                    unconditional
 *    C1  (pbvlshr (pbvlshr x y) z)
 *          ->  ite(pbvuge (pbvadd y z) y, pbvlshr x (pbvadd y z), 0)
 *    C2  (pbvshl  (pbvshl  x y) z)   -- same shape
 *    The guard is NOT optional.  y+z is computed mod 2^k and can wrap: at
 *    k=8, y=z=128 gives y+z=0, so the naive merge yields x while the true
 *    result is 0.  `pbvuge (pbvadd y z) y` is exactly "the addition did not
 *    overflow".  When it holds, y+z is the true sum and the shift already
 *    yields 0 for sums >= k.  When it fails, y+z >= 2^k, so at least one of
 *    y,z is >= 2^(k-1) >= k and the true result is 0.  Hence the ite is exact.
 *
 *    pbvashr is EXCLUDED: it fills with the sign bit, so the overflow branch
 *    is not the zero constant and the merge saturates at k-1 instead.
 *
 * D. NESTED EXTENSION MERGE                  unconditional
 *    D1  (pzero_extend n (pzero_extend m x))  ->  (pzero_extend (n+m) x)
 *    D2  (psign_extend n (psign_extend m x))  ->  (psign_extend (n+m) x)
 *    The MIXED forms are unsound and absent: zext(n, sext(m,x)) pads with
 *    zeros where sext would replicate the sign bit, and sext(n, zext(m,x))
 *    only collapses when m > 0 forces the inner top bit to 0.
 *
 * ===========================================================================
 * EXTENSION NORMALIZATION  (each family behind its own flag; all six are
 *                           selected together by --pbv-mw-ext-norm)
 * ===========================================================================
 *
 * T. TRUNCATION PUSH                              (--pbv-mw-trunc-push)
 *    Write k = i + 1 for the width of the low extract t[i:0].
 *    T0  t[i:0]                      ->  t                when w(t) = k
 *    T1  (EXT n x)[i:0]              ->  x                when w(x) = k
 *                                    ->  x[i:0]           when k <= w(x)
 *                                    ->  (EXT (k-w(x)) x) when w(x) <= k
 *    T2  (OP a b ...)[i:0]           ->  (OP a[i:0] b[i:0] ...)
 *        for OP in {add, sub, mul, and, or, xor, not, neg}: the low k bits of
 *        each depend only on the low k bits of its operands.
 *    T3  (ite c a b)[i:0]            ->  (ite c a[i:0] b[i:0])
 *    T4  (y[h:0])[i:0]               ->  y[i:0]
 *    T5  (a << s)[i:0]  with a = (psign_extend n x), k <= w(x)
 *                                    ->  ((pzero_extend n x) << s)[i:0]
 *        The low k bits of a << s depend only on the low k bits of a, where
 *        the two extensions agree.
 *    Each pushed extract is normalized again, so a chain reaches the leaves.
 *    Rule B above needs an extension of EXACTLY width k as an operand and
 *    does not revisit what it builds, so it stops after one step.
 *
 * L. LOW MASK                                     (--pbv-mw-low-mask)
 *    L1  t & (pzero_extend n ONES_k)  ->  (pzero_extend n t[k-1:0])
 *    L2  t & ONES                     ->  t
 *    L3  t & (pzero_extend n x)       ->  (pzero_extend n (t[k-1:0] & x))
 *        for a k-bit x; L1 is the case x = ONES_k, folded further.
 *    ONES_k is (pbvnot (int_to_pbv k 0)) or (int_to_pbv k -1). No side
 *    condition: the operands have equal widths, so t is (k+n)-bit.
 *
 * X. EXTENSIONS THROUGH BITWISE OPERATORS         (--pbv-mw-ext-bitwise)
 *    X1  OP(EXT n a, EXT n b)  ->  EXT n (OP a b)   OP in {and, or, xor}
 *        same EXT kind, w(a) = w(b). When w(a) <= w(b) is entailed instead,
 *        a is first aligned: EXT (t-w(a)) a = EXT (t-w(b)) (EXT (w(b)-w(a)) a).
 *    X2  pbvnot (psign_extend n a)  ->  psign_extend n (pbvnot a)
 *    X3  (= (EXT n a) (EXT n b))    ->  (= a b)     same kind, w(a) = w(b);
 *        both extensions are injective.
 *    X4  a & ~a -> 0,  a | ~a -> ONES,  a ^ ~a -> ONES
 *    X5  EXT n (int_to_pbv w 0)     ->  int_to_pbv (w+n) 0
 *
 * S. ONE-BIT SIGN EXTENSION                       (--pbv-mw-sext-bv1)
 *    S1  psign_extend n c  ->  pbvneg (pzero_extend n c)     when w(c) = 1
 *        sext(1) is all ones, which is -1 = -zext(1); sext(0) = 0 = -zext(0).
 *    S2  pbvsub a (pbvneg b)  ->  pbvadd a b
 *    S3  sext(c) & t  ->  ite(c = 1, t, 0)       when w(c) = 1
 *        sext(c) | t  ->  ite(c = 1, ONES, t)
 *        sext(c) ^ t  ->  ite(c = 1, ~t, t)
 *        Under a bitwise operator the extension is a mask, all ones or all
 *        zeros by c; S1's form -(zext c) is matched too. Without S3, S1 turns
 *        the mask into a piand over a negation, which NIA handles far worse.
 *
 * I. EXTENSION IDIOMS                             (--pbv-mw-sext-idioms)
 *    I1  EXT n (EXT m x)        ->  EXT (n+m) x            same kind
 *    I2  EXT n (ite c a b)      ->  ite c (EXT n a) (EXT n b)
 *    I3  (a << K) >>s K         ->  psign_extend m a[w-m-1:0]
 *        for a w-bit a and K = (int_to_pbv w m), when 0 <= m <= w-1.
 *        Shifting left by m drops the top m bits, and the arithmetic shift
 *        back refills them with the sign of what is now bit w-m-1.
 *
 * R. SIGNED RANGE                                 (--learned-rewrite-rules=signed-range)
 *    C = (pbvshl -1 (int_to_pbv W m)) is exactly -2^m when m + 1 <= W, and
 *    (psign_extend n x) of a p-bit x is >= -2^(p-1). When p <= m:
 *    R1  C <s sext(x),  C <=s sext(x)   ->  true
 *    R2  sext(x) <s C,  sext(x) <=s C   ->  false
 *
 * W. SHIFTS THROUGH BITWISE OPERATORS             (--pbv-mw-shift-bitwise)
 *    A shift only moves bit positions, filling with 0 (shl/lshr) or with the
 *    sign (ashr), and 0 OP 0 = 0 for OP in and/or/xor, so:
 *    W1  (a OP b) SH c          ->  (a SH c) OP (b SH c)      SH in shl/lshr/ashr
 *        ~a >>s c               ->  ~(a >>s c)                (ashr only)
 *    W2  (x << c) >> c          ->  x & (ones >> c)
 *        (x >> c) << c          ->  x & (ones << c)
 *    W3  (y >> c) & (ones >> c) ->  y >> c     (likewise <<): the mask is
 *        all ones wherever the shifted value can be non-zero
 *    W4  OP(EXT n a, EXT n b)   ->  EXT n (OP a b)   for the SAME n node: the
 *        operands' equal widths force w(a) = w(b), no width fact needed
 *    W5  and/or/xor chains are flattened, sorted, deduplicated (x^x
 *        cancels) and their 0/ones operands folded
 *    Every `(pbvsize v)` is first replaced by the size of its width class's
 *    representative (classes from the equal-width operators), so constants
 *    built at different but equal widths become the same node.
 *
 * G. SIGN IDIOMS                                  (--pbv-mw-sign-idioms)
 *    G1  (x & (1 << (w-1))) = 0 ->  ~(x <s 0)
 *    G2  -1 <s x, 0 <=s x       ->  ~(x <s 0);    x <=s -1  ->  x <s 0
 *        (x >s y and x >=s y against 0/-1 are first read as y <s x, y <=s x)
 *    G3  m >>s (w-1)            ->  ite(m <s 0, ones, 0)
 *    G4  OP(ite(c, k1, k2), y)  ->  ite(c, OP(k1, y), OP(k2, y))  for
 *        constant k1, k2 in {0, ones} and OP in and/or/xor
 *    G5  ite(c, a, b) + z       ->  ite(c, a + z, b + z)  when a branch is 0
 *        or subtracts z;  (y - z) + z -> y;  0 + y -> y
 *    G6  ite(~c, a, b)          ->  ite(c, b, a)
 *
 * K. MASK FACTS                                   (--learned-rewrite-rules=mask-facts)
 *    Facts read off the top-level conjuncts: M is a low mask 2^k - 1 when
 *    `((M+1) & ((M+1) - 1)) = 0` is asserted; p, q are disjoint when
 *    `p & q = 0` is; p, q are complements when `p = ~q` is.
 *    K1  M <u x                 ->  (x & ~M) != 0         M a low mask
 *        x <=u M                ->  (x & ~M) = 0
 *    K2  M & (a - b)            ->  M & ((M & a') - (M & b'))   M a low mask;
 *        the low k bits of a difference depend only on the low k bits of
 *        its operands, and a', b' drop every xor/or operand disjoint from M
 *    K3  ite(x & m = 0, x & m', x)  ->  x        m, m' complements: when x
 *        has no bit of m, x & ~m is x
 *    K4  (~a | b) = ones        ->  (a & b) = a    w(ones) = w(a)
 *        (--learned-rewrite-rules=subset-facts): both say every bit of a is
 *        a bit of b; the right side keeps no complement and no ones constant,
 *        so after int-blasting a subset fact is the single piand(k,a,b) = a
 */

#include "preprocessing/passes/pbv_mw.h"

#include <algorithm>
#include <set>
#include <unordered_set>

#include "expr/node_builder.h"
#include "util/rational.h"
#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

PbvMw::PbvMw(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "pbv-mw"), d_facts(preprocContext->getEnv())
{
}

PbvMw::PbvMw(PreprocessingPassContext* preprocContext,
             const std::string& name,
             const LearnedRewriteRules& cond)
    : PreprocessingPass(preprocContext, name),
      d_cond(cond),
      d_facts(preprocContext->getEnv())
{
}

TNode PbvMw::stripZext(TNode n)
{
  TNode t = n;
  while (t.getKind() == Kind::PBV_ZERO_EXTEND && t.getNumChildren() == 2)
  {
    t = t[1];
  }
  return t;
}

bool PbvMw::isExtend(TNode n)
{
  Kind k = n.getKind();
  return k == Kind::PBV_ZERO_EXTEND || k == Kind::PBV_SIGN_EXTEND;
}

bool PbvMw::isPushOp(Kind k)
{
  // pbvand deliberately omitted - see the header comment (would loop with
  // the RARE rule pbv-reverse-extract-and).
  return k == Kind::PBV_OR || k == Kind::PBV_XOR || k == Kind::PBV_ADD
         || k == Kind::PBV_SUB || k == Kind::PBV_MULT;
}

bool PbvMw::isLowMask(TNode t, Node& m)
{
  // (pbvsub (pbvshl (int_to_pbv w 1) (int_to_pbv w m)) (int_to_pbv w 1))
  if (t.getKind() != Kind::PBV_SUB || t.getNumChildren() != 2
      || t[0].getKind() != Kind::PBV_SHL || t[0].getNumChildren() != 2
      || t[0][0].getKind() != Kind::INT_TO_PBV
      || t[0][1].getKind() != Kind::INT_TO_PBV
      || t[1].getKind() != Kind::INT_TO_PBV)
  {
    return false;
  }
  if (!t[0][0][1].isConst() || t[0][0][1].getConst<Rational>() != Rational(1)
      || !t[1][1].isConst() || t[1][1].getConst<Rational>() != Rational(1))
  {
    return false;
  }
  m = t[0][1][1];
  return true;
}

bool PbvMw::isOnes(TNode t)
{
  if (t.getKind() == Kind::PBV_NOT && t.getNumChildren() == 1)
  {
    return isZero(t[0]);
  }
  // -1 written as the negation of one
  if (t.getKind() == Kind::PBV_NEG && t.getNumChildren() == 1)
  {
    TNode u = t[0];
    return u.getKind() == Kind::INT_TO_PBV && u.getNumChildren() == 2
           && u[1].isConst() && u[1].getConst<Rational>() == Rational(1);
  }
  return t.getKind() == Kind::INT_TO_PBV && t.getNumChildren() == 2
         && t[1].isConst() && t[1].getConst<Rational>() == Rational(-1);
}

bool PbvMw::isZero(TNode t)
{
  return t.getKind() == Kind::INT_TO_PBV && t.getNumChildren() == 2
         && t[1].isConst() && t[1].getConst<Rational>().sgn() == 0;
}

void PbvMw::bump(const char* rule) { d_fired[rule]++; }

/* == CAUSE 2: harvest the pbvsize <-> width-variable links ================= */

void PbvMw::harvestFrom(TNode a)
{
  if (a.getKind() == Kind::AND)
  {
    for (const Node& c : a)
    {
      harvestFrom(c);
    }
    return;
  }
  if (a.isClosure())
  {
    return;
  }
  if (a.getKind() != Kind::EQUAL || a.getNumChildren() != 2)
  {
    return;
  }
  for (size_t i = 0; i < 2; ++i)
  {
    TNode l = a[i];
    TNode r = a[1 - i];
    if (l.getKind() == Kind::PBV_SIZE && r.getType().isInteger()
        && r.getKind() != Kind::PBV_SIZE)
    {
      // Keep the first link seen; later duplicates are equal anyway.
      d_sizeAlias.emplace(Node(l), Node(r));
    }
  }
}

void PbvMw::harvestUltFrom(TNode a)
{
  if (a.getKind() == Kind::AND)
  {
    for (const Node& c : a)
    {
      harvestUltFrom(c);
    }
    return;
  }
  if (a.isClosure())
  {
    return;
  }
  // `(pbvult t (int_to_pbv w m))` says the VALUE of t is below m. That is how
  // a width-parametric goal states that a shift amount is in range, and it is
  // exactly the side condition rule M3 needs.
  if (a.getKind() != Kind::PBV_ULT || a.getNumChildren() != 2)
  {
    return;
  }
  TNode b = a[1];
  if (b.getKind() != Kind::INT_TO_PBV || b.getNumChildren() != 2)
  {
    return;
  }
  d_ultBound.emplace(stripZext(a[0]), Node(b[1]));
}

void PbvMw::harvestUltBounds(const std::vector<Node>& assertions)
{
  for (const Node& a : assertions)
  {
    harvestUltFrom(a);
  }
}

void PbvMw::harvestWidths(const std::vector<Node>& assertions)
{
  for (const Node& a : assertions)
  {
    harvestFrom(a);
  }
}

/* == widths ================================================================ */

Node PbvMw::widthOf(TNode t)
{
  auto it = d_widthCache.find(t);
  if (it != d_widthCache.end())
  {
    return it->second;
  }
  NodeManager* nm = nodeManager();
  Node one = nm->mkConstInt(Rational(1));
  Node res;
  Kind k = t.getKind();
  switch (k)
  {
    case Kind::INT_TO_PBV: res = t[0]; break;
    case Kind::PBV_EXTRACT:
      // i - j + 1
      res = nm->mkNode(Kind::ADD, nm->mkNode(Kind::SUB, t[1], t[2]), one);
      break;
    case Kind::PBV_ZERO_EXTEND:
    case Kind::PBV_SIGN_EXTEND:
      res = nm->mkNode(Kind::ADD, widthOf(t[1]), t[0]);
      break;
    case Kind::PBV_CONCAT:
    {
      std::vector<Node> parts;
      for (const Node& c : t)
      {
        parts.push_back(widthOf(c));
      }
      res = parts.size() == 1 ? parts[0] : nm->mkNode(Kind::ADD, parts);
      break;
    }
    case Kind::ITE: res = widthOf(t[1]); break;
    default:
    {
      if (t.getNumChildren() >= 1 && t[0].getType().isPbv())
      {
        // Equal-width operators: the width of the first operand.
        res = widthOf(t[0]);
        break;
      }
      // A leaf PBV term: use its pbvsize, resolved through the alias map so
      // the result is stated in the user's own width variable (CAUSE 2).
      Node sz = nm->mkNode(Kind::PBV_SIZE, Node(t));
      auto ait = d_sizeAlias.find(sz);
      res = (ait == d_sizeAlias.end()) ? sz : ait->second;
      break;
    }
  }
  res = rewrite(res);
  d_widthCache[t] = res;
  return res;
}

bool PbvMw::widthEq(Node a, Node b)
{
  if (a == b)
  {
    return true;
  }
  // CAUSE 1: normalise through the arithmetic rewriter instead of comparing
  // node structure, so `(- r 1)` and `(+ (- 1) r)` are recognised as equal.
  Node d = rewrite(nodeManager()->mkNode(Kind::SUB, a, b));
  return d.isConst() && d.getConst<Rational>().sgn() == 0;
}

bool PbvMw::widthPositive(TNode m)
{
  if (d_facts.geqConst(m, Rational(1)))
  {
    return true;
  }
  // A width is positive by construction. Adm(phi) says so too, but it is
  // stated by pbv-to-int, which runs after this pass.
  if (m.getKind() == Kind::PBV_SIZE)
  {
    return true;
  }
  // ... including when the goal named it, e.g. `(= (pbvsize x) k)` makes the
  // user's `k` a width, and widthOf() reports widths in that spelling.
  for (const auto& [sz, alias] : d_sizeAlias)
  {
    if (alias == m)
    {
      return true;
    }
  }
  return false;
}

bool PbvMw::widthLeq(Node a, Node b)
{
  return widthEq(a, b) || d_facts.leq(a, b);
}

bool PbvMw::admissible(TNode t)
{
  NodeManager* nm = nodeManager();
  Node one = nm->mkConstInt(Rational(1));
  auto atLeastOne = [&](Node w) {
    w = rewrite(w);
    return widthPositive(w) || d_facts.geqConst(w, Rational(1));
  };
  auto nonNeg = [&](Node e) {
    e = rewrite(e);
    return d_facts.geqConst(e, Rational(0)) || d_facts.nonNeg(e)
           || widthPositive(e);
  };
  switch (t.getKind())
  {
    case Kind::INT_TO_PBV: return atLeastOne(t[0]);
    case Kind::PBV_ZERO_EXTEND:
    case Kind::PBV_SIGN_EXTEND: return nonNeg(t[0]);
    case Kind::PBV_EXTRACT:
      // 0 <= j, i - j + 1 >= 1, i + 1 <= w(t)
      return nonNeg(t[2])
             && atLeastOne(nm->mkNode(
                 Kind::ADD, nm->mkNode(Kind::SUB, t[1], t[2]), one))
             && widthLeq(rewrite(nm->mkNode(Kind::ADD, t[1], one)),
                         widthOf(t[0]));
    case Kind::ITE: return widthEq(widthOf(t[1]), widthOf(t[2]));
    default: break;
  }
  // Every other operator over PBV operands needs them at one width.
  Node w;
  for (const Node& c : t)
  {
    if (!c.getType().isPbv())
    {
      continue;
    }
    Node wc = widthOf(c);
    if (w.isNull())
    {
      w = wc;
    }
    else if (!widthEq(w, wc))
    {
      return false;
    }
  }
  return true;
}

void PbvMw::pinAdmissibility(const std::vector<Node>& assertions,
                             std::vector<Node>& out)
{
  NodeManager* nm = nodeManager();
  Node zero = nm->mkConstInt(Rational(0));
  Node one = nm->mkConstInt(Rational(1));
  std::unordered_set<Node> seen;
  std::unordered_set<Node> added;
  auto add = [&](Node c) {
    c = rewrite(c);
    if (c.isConst() && c.getConst<bool>())
    {
      return;
    }
    if (added.insert(c).second)
    {
      out.push_back(c);
    }
  };
  std::vector<TNode> stack(assertions.begin(), assertions.end());
  while (!stack.empty())
  {
    TNode t = stack.back();
    stack.pop_back();
    // Inside a quantifier the int-blaster routes Adm to the quantifier's
    // guard, so it is not a top-level fact; leave those terms alone.
    if (!seen.insert(t).second || t.isClosure())
    {
      continue;
    }
    Kind k = t.getKind();
    if (t.getType().isPbv() && (t.getNumChildren() == 0 || k == Kind::APPLY_UF))
    {
      add(nm->mkNode(Kind::GEQ, widthOf(t), one));
    }
    switch (k)
    {
      case Kind::INT_TO_PBV: add(nm->mkNode(Kind::GEQ, t[0], one)); break;
      case Kind::PBV_EXTRACT:
        add(nm->mkNode(Kind::LEQ, zero, t[2]));
        add(nm->mkNode(Kind::LEQ, t[2], t[1]));
        add(nm->mkNode(Kind::LT, t[1], widthOf(t[0])));
        break;
      case Kind::PBV_ZERO_EXTEND:
      case Kind::PBV_SIGN_EXTEND:
        add(nm->mkNode(Kind::LEQ, zero, t[0]));
        break;
      case Kind::ITE:
        if (t[1].getType().isPbv())
        {
          add(nm->mkNode(Kind::EQUAL, widthOf(t[1]), widthOf(t[2])));
        }
        break;
      // Operands of any width.
      case Kind::PBV_CONCAT:
      case Kind::APPLY_UF: break;
      default:
      {
        // Every other operator over PBV operands needs them at one width.
        Node w;
        for (const Node& c : t)
        {
          if (!c.getType().isPbv())
          {
            continue;
          }
          if (w.isNull())
          {
            w = widthOf(c);
          }
          else
          {
            add(nm->mkNode(Kind::EQUAL, w, widthOf(c)));
          }
        }
        break;
      }
    }
    for (const Node& c : t)
    {
      stack.push_back(c);
    }
  }
}

/* == extension normalization =============================================== */

Node PbvMw::mkLowExtract(TNode t, Node i)
{
  NodeManager* nm = nodeManager();
  return rewriteRec(
      nm->mkNode(Kind::PBV_EXTRACT, t, rewrite(i), nm->mkConstInt(Rational(0))));
}

Node PbvMw::applyExtNorm(Node n)
{
  const options::HolderSMT& o = options().smt;
  NodeManager* nm = nodeManager();
  Node one = nm->mkConstInt(Rational(1));
  Kind k = n.getKind();
  size_t nc = n.getNumChildren();

  // --- T : truncation push  (--pbv-mw-trunc-push)
  // Every T rule deletes the extract and most delete the node under it, so
  // both must be admissible.
  if ((o.pbvMwTruncPush || d_cond.d_truncPush) && k == Kind::PBV_EXTRACT
      && nc == 3
      && n[2].isConst() && n[2].getConst<Rational>().sgn() == 0
      && admissible(n))
  {
    Node i = n[1];
    Node kw = rewrite(nm->mkNode(Kind::ADD, i, one));
    TNode t = n[0];
    Kind tk = t.getKind();
    // T0 (conditional, learned-rewrite-pbv): the extract keeps every bit.
    {
      Node r = lrTruncPushFull(n, t, kw);
      if (r != n)
      {
        return r;
      }
    }
    if (!admissible(t))
    {
      return n;
    }
    // T1, T4, T5 (conditional, learned-rewrite-pbv). Each matches a kind of t
    // that T2 and T3 do not, so calling them first keeps the rule order.
    {
      Node r = lrTruncPushCut(n, t, i, kw);
      if (r != n)
      {
        return r;
      }
    }
    if (!o.pbvMwTruncPush)
    {
      return n;
    }
    // T2: through an operator whose low bits depend only on low bits.
    if (tk == Kind::PBV_ADD || tk == Kind::PBV_SUB || tk == Kind::PBV_MULT
        || tk == Kind::PBV_AND || tk == Kind::PBV_OR || tk == Kind::PBV_XOR
        || tk == Kind::PBV_NOT || tk == Kind::PBV_NEG)
    {
      std::vector<Node> kids;
      for (const Node& c : t)
      {
        kids.push_back(mkLowExtract(c, i));
      }
      bump("T2-push-op");
      return nm->mkNode(tk, kids);
    }
    // T3: through an ITE.
    if (tk == Kind::ITE)
    {
      bump("T3-push-ite");
      return nm->mkNode(
          Kind::ITE, t[0], mkLowExtract(t[1], i), mkLowExtract(t[2], i));
    }
  }

  // --- L : low mask  (--pbv-mw-low-mask)
  // The ONES constant inside a mask must itself be admissible.
  auto onesAdmissible = [&](TNode c) {
    return c.getKind() == Kind::INT_TO_PBV ? admissible(c) : admissible(c[0]);
  };
  if (o.pbvMwLowMask && k == Kind::PBV_AND && admissible(n))
  {
    for (size_t j = 0; j < nc; ++j)
    {
      TNode m = n[j];
      bool l1 = m.getKind() == Kind::PBV_ZERO_EXTEND && m.getNumChildren() == 2
                && isOnes(m[1]) && admissible(m) && onesAdmissible(m[1]);
      if (!l1 && !(isOnes(m) && onesAdmissible(m)))
      {
        continue;
      }
      std::vector<Node> rest;
      for (size_t r = 0; r < nc; ++r)
      {
        if (r != j)
        {
          rest.push_back(n[r]);
        }
      }
      Node t = rest.size() == 1 ? rest[0] : nm->mkNode(Kind::PBV_AND, rest);
      if (!l1)
      {
        bump("L2-and-ones");
        return t;
      }
      Node kw = widthOf(m[1]);
      bump("L1-low-mask");
      return nm->mkNode(
          Kind::PBV_ZERO_EXTEND,
          m[0],
          mkLowExtract(t, nm->mkNode(Kind::SUB, kw, one)));
    }
    // L3: a conjunction with any zero extension keeps only the low bits.
    for (size_t j = 0; j < nc; ++j)
    {
      TNode m = n[j];
      if (m.getKind() != Kind::PBV_ZERO_EXTEND || m.getNumChildren() != 2
          || !admissible(m))
      {
        continue;
      }
      std::vector<Node> rest;
      for (size_t r = 0; r < nc; ++r)
      {
        if (r != j)
        {
          rest.push_back(n[r]);
        }
      }
      Node t = rest.size() == 1 ? rest[0] : nm->mkNode(Kind::PBV_AND, rest);
      Node kw = widthOf(m[1]);
      bump("L3-and-zext");
      return nm->mkNode(
          Kind::PBV_ZERO_EXTEND,
          m[0],
          rewriteRec(nm->mkNode(
              Kind::PBV_AND,
              mkLowExtract(t, nm->mkNode(Kind::SUB, kw, one)),
              m[1])));
    }
  }

  {
    Node r = lrExtBitwise(n);
    if (r != n)
    {
      return r;
    }
  }
  if (o.pbvMwExtBitwise)
  {
    // --- X4 : an operand against its own negation
    if ((k == Kind::PBV_AND || k == Kind::PBV_OR || k == Kind::PBV_XOR)
        && nc == 2)
    {
      for (size_t s = 0; s < 2; ++s)
      {
        if (n[s].getKind() == Kind::PBV_NOT && n[s][0] == n[1 - s])
        {
          Node w = widthOf(n);
          Node zero = nm->mkNode(Kind::INT_TO_PBV, w, nm->mkConstInt(Rational(0)));
          bump("X4-complement");
          return k == Kind::PBV_AND ? zero : nm->mkNode(Kind::PBV_NOT, zero);
        }
      }
    }
    // --- X1 (conditional): in lrExtBitwise above
    // --- X2 : not commutes with a sign extension
    if (k == Kind::PBV_NOT && nc == 1
        && n[0].getKind() == Kind::PBV_SIGN_EXTEND
        && n[0].getNumChildren() == 2 && admissible(n[0]))
    {
      bump("X2-not-through-sext");
      return nm->mkNode(Kind::PBV_SIGN_EXTEND,
                        n[0][0],
                        rewriteRec(nm->mkNode(Kind::PBV_NOT, n[0][1])));
    }
    // --- X3 (conditional): in lrExtBitwise above
    // --- X5 : extension of zero
    if (isExtend(n) && nc == 2 && isZero(n[1]) && admissible(n)
        && admissible(n[1]))
    {
      bump("X5-ext-zero");
      return nm->mkNode(Kind::INT_TO_PBV,
                        widthOf(n),
                        nm->mkConstInt(Rational(0)));
    }
  }

  // --- S1, S3 (conditional, learned-rewrite-pbv)
  {
    Node r = lrSextBv1(n);
    if (r != n)
    {
      return r;
    }
  }
  if (o.pbvMwSextBv1)
  {
    // --- S2 : a - (-b) = a + b
    if (k == Kind::PBV_SUB && nc == 2 && n[1].getKind() == Kind::PBV_NEG)
    {
      bump("S2-sub-neg");
      return nm->mkNode(Kind::PBV_ADD, n[0], n[1][0]);
    }
  }

  if (o.pbvMwSextIdioms)
  {
    // --- I1 : nested extensions of the same kind
    if (isExtend(n) && nc == 2 && n[1].getKind() == k
        && n[1].getNumChildren() == 2 && admissible(n) && admissible(n[1]))
    {
      bump("I1-merge-ext");
      return nm->mkNode(
          k, rewrite(nm->mkNode(Kind::ADD, n[0], n[1][0])), n[1][1]);
    }
    // --- I2 : an extension into an ITE
    if (isExtend(n) && nc == 2 && n[1].getKind() == Kind::ITE
        && admissible(n[1]))
    {
      bump("I2-ext-into-ite");
      return nm->mkNode(Kind::ITE,
                        n[1][0],
                        rewriteRec(nm->mkNode(k, n[0], n[1][1])),
                        rewriteRec(nm->mkNode(k, n[0], n[1][2])));
    }
  }
  // --- I3 (conditional, learned-rewrite-pbv)
  {
    Node r = lrSextIdioms(n);
    if (r != n)
    {
      return r;
    }
  }

  // --- R (conditional, learned-rewrite-pbv)
  return lrSignedRange(n);
}

/* == rewriting ============================================================= */

/* == the RW_B table (--pbv-rewrites-min) =================================== */

bool PbvMw::isWidthMinusOne(TNode s, Node& k)
{
  Node w = widthMinusOne(s);
  if (!w.isNull())
  {
    k = w;
    return true;
  }
  if (s.getKind() == Kind::INT_TO_PBV && s.getNumChildren() == 2
      && widthEq(s[1],
                 nodeManager()->mkNode(
                     Kind::SUB, s[0], nodeManager()->mkConstInt(Rational(1)))))
  {
    k = s[0];
    return true;
  }
  return false;
}

Node PbvMw::applyMin(Node n)
{
  const options::HolderSMT& o = options().smt;
  if (!o.pbvRewritesMin)
  {
    return n;
  }
  NodeManager* nm = nodeManager();
  Kind k = n.getKind();
  size_t nc = n.getNumChildren();
  auto isBitwise = [](Kind kk) {
    return kk == Kind::PBV_AND || kk == Kind::PBV_OR || kk == Kind::PBV_XOR;
  };
  auto isShiftK = [](Kind kk) {
    return kk == Kind::PBV_SHL || kk == Kind::PBV_LSHR || kk == Kind::PBV_ASHR;
  };
  // the ONES constant inside a mask must itself be admissible
  auto onesAdmissible = [&](TNode c) {
    return c.getKind() == Kind::INT_TO_PBV ? admissible(c) : admissible(c[0]);
  };
  auto isOnesShift = [&](TNode m, Kind sk) {
    return m.getKind() == sk && isOnes(m[0]) && admissible(m)
           && onesAdmissible(m[0]);
  };
  const bool binBitwise = isBitwise(k) && nc == 2;

  if (k == Kind::PBV_AND && nc == 2 && admissible(n))
  {
    for (size_t i = 0; i < 2; ++i)
    {
      TNode m = n[i], x = n[1 - i];
      // and-lshr-mask: (~0 >> z) & (x >> z) -> x >> z. Ahead of shl-lshr and
      // shift-bitwise, which also match and would leave a mask behind.
      if (isOnesShift(m, Kind::PBV_LSHR) && x.getKind() == Kind::PBV_LSHR
          && x[1] == m[1] && admissible(x))
      {
        bump("min-and-lshr-mask");
        return x;
      }
    }
    // shl-lshr / lshr-shl, skipped under W2 (their inverse)
    for (size_t i = 0; i < 2 && !d_cond.d_shiftBitwise; ++i)
    {
      TNode m = n[i], x = n[1 - i];
      // x & (~0 >> z) -> (x << z) >> z
      if (isOnesShift(m, Kind::PBV_LSHR))
      {
        bump("min-shl-lshr");
        return nm->mkNode(
            Kind::PBV_LSHR, nm->mkNode(Kind::PBV_SHL, x, m[1]), m[1]);
      }
      // x & (~0 << z) -> (x >> z) << z
      if (isOnesShift(m, Kind::PBV_SHL))
      {
        bump("min-lshr-shl");
        return nm->mkNode(
            Kind::PBV_SHL, nm->mkNode(Kind::PBV_LSHR, x, m[1]), m[1]);
      }
    }
  }

  // shift-bitwise: (x sh z) o (y sh z) -> (x o y) sh z, skipped under W1
  // (its inverse)
  if (binBitwise && !(o.pbvMwShiftBitwise && o.pbvMwShiftBitwiseW1)
      && isShiftK(n[0].getKind())
      && n[1].getKind() == n[0].getKind() && n[0][1] == n[1][1]
      && admissible(n) && admissible(n[0]) && admissible(n[1]))
  {
    bump("min-shift-bitwise");
    return nm->mkNode(n[0].getKind(),
                      rewriteRec(nm->mkNode(k, n[0][0], n[1][0])),
                      n[0][1]);
  }

  // bitwise-sext / bitwise-zext: ext(n,x) o ext(n,y) -> ext(n, x o y)
  if (binBitwise && isExtend(n[0]) && n[1].getKind() == n[0].getKind()
      && widthEq(n[0][0], n[1][0]) && admissible(n) && admissible(n[0])
      && admissible(n[1]))
  {
    bump("min-bitwise-ext");
    return nm->mkNode(n[0].getKind(),
                      n[0][0],
                      rewriteRec(nm->mkNode(k, n[0][1], n[1][1])));
  }

  // sext-sext / zext-zext: ext(n, ext(m, x)) -> ext(n+m, x)
  if (isExtend(n) && nc == 2 && n[1].getKind() == k && admissible(n)
      && admissible(n[1]))
  {
    bump("min-ext-ext");
    return nm->mkNode(
        k, rewrite(nm->mkNode(Kind::ADD, n[0], n[1][0])), n[1][1]);
  }

  // sext-zero / zext-zero: ext(n, 0) -> 0
  if (isExtend(n) && nc == 2 && isZero(n[1]) && admissible(n)
      && admissible(n[1]))
  {
    bump("min-ext-zero");
    return nm->mkNode(
        Kind::INT_TO_PBV, widthOf(n), nm->mkConstInt(Rational(0)));
  }

  // sext-ite / zext-ite: ite(c, ext(n,x), ext(n,y)) -> ext(n, ite(c,x,y)),
  // skipped under I2 (its inverse)
  if (k == Kind::ITE && !o.pbvMwSextIdioms && n.getType().isPbv()
      && isExtend(n[1]) && n[2].getKind() == n[1].getKind()
      && widthEq(n[1][0], n[2][0]) && admissible(n) && admissible(n[1])
      && admissible(n[2]))
  {
    bump("min-ext-ite");
    return nm->mkNode(
        n[1].getKind(),
        n[1][0],
        rewriteRec(nm->mkNode(Kind::ITE, n[0], n[1][1], n[2][1])));
  }

  // sign-bit-and: x & (1 << (k-1)) = 0 -> ~(x <s 0)
  if (k == Kind::EQUAL && n[0].getType().isPbv() && admissible(n))
  {
    for (size_t s = 0; s < 2; ++s)
    {
      TNode a = n[s], z = n[1 - s];
      if (!isZero(z) || a.getKind() != Kind::PBV_AND || a.getNumChildren() != 2
          || !admissible(a))
      {
        continue;
      }
      for (size_t j = 0; j < 2; ++j)
      {
        TNode m = a[j];
        Node w;
        if (m.getKind() == Kind::PBV_SHL && m[0].getKind() == Kind::INT_TO_PBV
            && m[0][1].isConst()
            && m[0][1].getConst<Rational>() == Rational(1)
            && isWidthMinusOne(m[1], w) && widthEq(w, m[0][0])
            && admissible(m))
        {
          bump("min-sign-bit-and");
          return nm->mkNode(Kind::PBV_SLT, a[1 - j], z).notNode();
        }
      }
    }
  }

  // ashr-sign: x >>a (k-1) -> ite(x <s 0, ~0, 0)
  {
    Node w;
    if (k == Kind::PBV_ASHR && nc == 2 && isWidthMinusOne(n[1], w)
        && admissible(n))
    {
      Node z = nm->mkNode(Kind::INT_TO_PBV, w, nm->mkConstInt(Rational(0)));
      bump("min-ashr-sign");
      return nm->mkNode(Kind::ITE,
                        nm->mkNode(Kind::PBV_SLT, n[0], z),
                        nm->mkNode(Kind::PBV_NOT, z),
                        z);
    }
  }

  // and/or/xor/add-ite-mask on m = ite(c, 0, ~0)
  if ((binBitwise || (k == Kind::PBV_ADD && nc == 2)) && admissible(n))
  {
    for (size_t i = 0; i < 2; ++i)
    {
      TNode m = n[i];
      Node x = n[1 - i];
      if (m.getKind() != Kind::ITE || !isZero(m[1]) || !isOnes(m[2])
          || !admissible(m))
      {
        continue;
      }
      TNode c = m[0];
      bump("min-ite-mask");
      switch (k)
      {
        // ite(c, 0, x)
        case Kind::PBV_AND: return nm->mkNode(Kind::ITE, c, m[1], x);
        // ite(c, x, ~0)
        case Kind::PBV_OR: return nm->mkNode(Kind::ITE, c, x, m[2]);
        // ite(c, x, ~x)
        case Kind::PBV_XOR:
          return nm->mkNode(Kind::ITE, c, x, nm->mkNode(Kind::PBV_NOT, x));
        // ite(c, x, x - 1)
        default:
          return nm->mkNode(
              Kind::ITE,
              c,
              x,
              nm->mkNode(Kind::PBV_SUB,
                         x,
                         nm->mkNode(Kind::INT_TO_PBV,
                                    m[1][0],
                                    nm->mkConstInt(Rational(1)))));
      }
    }
  }
  return n;
}

Node PbvMw::applyRules(Node n)
{
  NodeManager* nm = nodeManager();
  Node one = nm->mkConstInt(Rational(1));
  Kind k = n.getKind();

  {
    Node m = applyMin(n);
    if (m != n)
    {
      return m;
    }
  }
  {
    Node e = applyExtNorm(n);
    if (e != n)
    {
      return e;
    }
  }
  {
    Node b = applyBitwise(n);
    if (b != n)
    {
      return b;
    }
  }

  // --- G : zero extension commutes with a right shift (--pbv-shift-add-distrib)
  //
  //   zext(n, x >> y)  ->  (zext(n,x)) >> (zext(n,y))
  //
  // Sound with no side condition. A logical right shift is x div 2^y, and zext
  // changes no value: if y is below the original width both sides are x div 2^y,
  // and if y reaches it the original is 0 while the wider form is x div 2^y with
  // x < 2^w <= 2^y, so 0 as well.
  //
  // It exists to make rule F usable. F rewrites at the OUTER width, while the
  // other side of a multi-width goal shifts at the inner width and extends
  // afterwards; pushing the extension inside puts both in the same shape, and
  // pbv-merge-zext then collapses the stacked extensions.
  //
  // pbvshl is NOT included: a left shift discards the bits it pushes past the
  // width, so extending after the shift keeps them lost while extending before
  // keeps them -- the two are not equal.
  if (options().smt.pbvShiftAddDistrib && k == Kind::PBV_ZERO_EXTEND
      && n.getNumChildren() == 2 && n[1].getKind() == Kind::PBV_LSHR
      && n[1].getNumChildren() == 2)
  {
    Node amt = n[0];
    bump("G-zext-through-lshr");
    return nm->mkNode(
        Kind::PBV_LSHR,
        nm->mkNode(Kind::PBV_ZERO_EXTEND, amt, n[1][0]),
        nm->mkNode(Kind::PBV_ZERO_EXTEND, amt, n[1][1]));
  }

  // --- F, E, E2 (conditional): in lrRules below

  // --- M1 : pull a common left shift out of a conjunction (--pbv-mask-slice)
  //
  //   (a << z) & (b << z)  ->  (a & b) << z
  //
  // Unconditional. A left shift by z maps bit i to bit i+z and fills the low z
  // bits with zeros; both sides therefore agree bit for bit -- zero in the low
  // z bits, and (a & b) at i+z above them.
  //
  // It exists to expose M2: a masked shift is written with the shift on BOTH
  // operands, so the mask is not adjacent to the value until this fires.
  Node m1mask;
  if (options().smt.pbvMaskSlice != options::PbvMaskSliceMode::NONE
      && k == Kind::PBV_AND
      && n.getNumChildren() == 2 && n[0].getKind() == Kind::PBV_SHL
      && n[1].getKind() == Kind::PBV_SHL && n[0].getNumChildren() == 2
      && n[1].getNumChildren() == 2 && n[0][1] == n[1][1]
      // Only when one operand IS the mask. Unconditionally, this rule moves a
      // conjunction under a shift that the solver may have found easier where
      // it was: on a SAT instance it turned a 0.16s answer into a timeout. It
      // exists to expose M2, so it fires exactly when M2 has something to do.
      && (options().smt.pbvMaskSlice == options::PbvMaskSliceMode::ALL
          || isLowMask(n[0][0], m1mask) || isLowMask(n[1][0], m1mask)))
  {
    bump("M1-and-shl-distrib");
    // The conjunction is a NEW node: rewriteRec's fixed-point loop only
    // re-applies rules at the top, so rewrite it here or M2 never sees it.
    return nm->mkNode(
        Kind::PBV_SHL,
        rewriteRec(nm->mkNode(Kind::PBV_AND, n[0][0], n[1][0])),
        n[0][1]);
  }

  // --- F, E, E2, M2, M3, A/B (conditional, learned-rewrite-pbv). F is on a
  // lshr, E/E2 on a sign extension, M2 on a conjunction with a low-mask operand
  // and M3, A and B on a low extract -- none of them overlaps G or M1 above or
  // the extension-normalization and bitwise families, so running them here
  // keeps the order they always had.
  return lrRules(n);
}

/* == bitwise families (W, G, K) ============================================ */

Node PbvMw::widthMinusOne(TNode s)
{
  // int_to_pbv(K, K) - int_to_pbv(K, 1): the value K-1 at width K
  if (s.getKind() != Kind::PBV_SUB || s.getNumChildren() != 2) return Node::null();
  TNode a = s[0], b = s[1];
  if (a.getKind() != Kind::INT_TO_PBV || b.getKind() != Kind::INT_TO_PBV)
  {
    return Node::null();
  }
  if (a[1] != a[0] || a[0] != b[0] || !b[1].isConst()
      || b[1].getConst<Rational>() != Rational(1))
  {
    return Node::null();
  }
  return a[0];
}

bool PbvMw::isMsbMask(TNode t)
{
  // (pbvshl (int_to_pbv K 1) <K-1>)
  if (t.getKind() != Kind::PBV_SHL || t.getNumChildren() != 2) return false;
  TNode one = t[0];
  if (one.getKind() != Kind::INT_TO_PBV || !one[1].isConst()
      || one[1].getConst<Rational>() != Rational(1))
  {
    return false;
  }
  Node k = widthMinusOne(t[1]);
  return !k.isNull() && k == one[0];
}

Node PbvMw::widthLeaf(TNode t)
{
  while (true)
  {
    if (t.isVar() && t.getType().isPbv()) break;
    Kind k = t.getKind();
    if (k == Kind::INT_TO_PBV && t[0].getKind() == Kind::PBV_SIZE)
    {
      t = t[0][0];
      continue;
    }
    switch (k)
    {
      case Kind::PBV_NOT:
      case Kind::PBV_NEG:
      case Kind::PBV_AND:
      case Kind::PBV_OR:
      case Kind::PBV_XOR:
      case Kind::PBV_ADD:
      case Kind::PBV_SUB:
      case Kind::PBV_MULT:
      case Kind::PBV_UDIV:
      case Kind::PBV_UREM:
      case Kind::PBV_SHL:
      case Kind::PBV_LSHR:
      case Kind::PBV_ASHR: t = t[0]; continue;
      case Kind::ITE:
        if (!t.getType().isPbv()) return Node::null();
        t = t[1];
        continue;
      default: return Node::null();
    }
  }
  // find with path halving
  Node x = t;
  while (true)
  {
    auto it = d_widthParent.find(x);
    if (it == d_widthParent.end() || it->second == x) return x;
    auto it2 = d_widthParent.find(it->second);
    if (it2 != d_widthParent.end()) it->second = it2->second;
    x = it->second;
  }
}

Node PbvMw::widthTerm(TNode t)
{
  NodeManager* nm = nodeManager();
  Node leaf = widthLeaf(t);
  return nm->mkNode(Kind::PBV_SIZE, leaf.isNull() ? Node(t) : leaf);
}

void PbvMw::buildWidthClasses(const std::vector<Node>& assertions)
{
  std::unordered_set<TNode> visited;
  std::vector<TNode> stack(assertions.begin(), assertions.end());
  std::vector<Node> order;  // first-seen leaves, for deterministic reps
  auto unite = [&](Node a, Node b) {
    if (a.isNull() || b.isNull()) return;
    Node ra = widthLeaf(a), rb = widthLeaf(b);
    if (ra.isNull() || rb.isNull() || ra == rb) return;
    // the earlier-seen leaf stays the representative
    auto pa = std::find(order.begin(), order.end(), ra);
    auto pb = std::find(order.begin(), order.end(), rb);
    if (pb < pa) std::swap(ra, rb);
    d_widthParent[rb] = ra;
  };
  while (!stack.empty())
  {
    TNode n = stack.back();
    stack.pop_back();
    if (!visited.insert(n).second || n.isClosure()) continue;
    if (n.isVar() && n.getType().isPbv())
    {
      if (d_widthParent.find(n) == d_widthParent.end())
      {
        d_widthParent[n] = n;
        order.push_back(n);
      }
    }
    Kind k = n.getKind();
    bool equalWidth = false;
    switch (k)
    {
      case Kind::EQUAL: equalWidth = n[0].getType().isPbv(); break;
      case Kind::ITE: equalWidth = n.getType().isPbv(); break;
      case Kind::PBV_AND:
      case Kind::PBV_OR:
      case Kind::PBV_XOR:
      case Kind::PBV_ADD:
      case Kind::PBV_SUB:
      case Kind::PBV_MULT:
      case Kind::PBV_UDIV:
      case Kind::PBV_UREM:
      case Kind::PBV_SHL:
      case Kind::PBV_LSHR:
      case Kind::PBV_ASHR:
      case Kind::PBV_ULT:
      case Kind::PBV_ULE:
      case Kind::PBV_UGT:
      case Kind::PBV_UGE:
      case Kind::PBV_SLT:
      case Kind::PBV_SLE:
      case Kind::PBV_SGT:
      case Kind::PBV_SGE: equalWidth = true; break;
      default: break;
    }
    if (equalWidth)
    {
      size_t first = k == Kind::ITE ? 1 : 0;
      for (size_t i = first + 1; i < n.getNumChildren(); ++i)
      {
        unite(n[first], n[i]);
      }
    }
    for (const Node& c : n) stack.push_back(c);
  }
  NodeManager* nm = nodeManager();
  for (const Node& v : order)
  {
    Node r = widthLeaf(v);
    if (r != v)
    {
      d_widthSubst[nm->mkNode(Kind::PBV_SIZE, v)] = nm->mkNode(Kind::PBV_SIZE, r);
    }
  }
}

void PbvMw::harvestMaskFacts(const std::vector<Node>& assertions)
{
  std::vector<TNode> conj(assertions.begin(), assertions.end());
  auto isOne = [](TNode t) {
    return t.getKind() == Kind::INT_TO_PBV && t[1].isConst()
           && t[1].getConst<Rational>() == Rational(1);
  };
  for (size_t i = 0; i < conj.size(); ++i)
  {
    TNode a = conj[i];
    if (a.getKind() == Kind::AND)
    {
      conj.insert(conj.end(), a.begin(), a.end());
      continue;
    }
    if (a.getKind() != Kind::EQUAL || !a[0].getType().isPbv()) continue;
    for (size_t s = 0; s < 2; ++s)
    {
      TNode l = a[s], r = a[1 - s];
      // p = ~q
      if (r.getKind() == Kind::PBV_NOT)
      {
        d_complementFacts.emplace(l, r[0]);
        d_complementFacts.emplace(r[0], l);
      }
      if (!isZero(r) || l.getKind() != Kind::PBV_AND || l.getNumChildren() != 2)
      {
        continue;
      }
      // p & q = 0
      d_disjointFacts.emplace(l[0], l[1]);
      d_disjointFacts.emplace(l[1], l[0]);
      // y & (y - 1) = 0 with y = M + 1: M is a low mask
      for (size_t j = 0; j < 2; ++j)
      {
        TNode y = l[j], d = l[1 - j];
        if (d.getKind() != Kind::PBV_SUB || d.getNumChildren() != 2
            || d[0] != y || !isOne(d[1]))
        {
          continue;
        }
        if (y.getKind() == Kind::PBV_ADD && y.getNumChildren() == 2)
        {
          for (size_t q = 0; q < 2; ++q)
          {
            if (isOne(y[1 - q])) d_lowMaskFacts.insert(y[q]);
          }
        }
      }
      // (M + 1) & M = 0, the same fact as written in the paper: M is a low
      // mask
      for (size_t j = 0; j < 2; ++j)
      {
        TNode y = l[j], m = l[1 - j];
        if (y.getKind() != Kind::PBV_ADD || y.getNumChildren() != 2)
        {
          continue;
        }
        for (size_t q = 0; q < 2; ++q)
        {
          if (y[q] == m && isOne(y[1 - q])) d_lowMaskFacts.insert(m);
        }
      }
    }
  }
}

bool PbvMw::areDisjoint(TNode a, TNode b) const
{
  return d_disjointFacts.count({a, b}) > 0;
}

bool PbvMw::areComplements(TNode a, TNode b) const
{
  if (a.getKind() == Kind::PBV_NOT && a[0] == b) return true;
  if (b.getKind() == Kind::PBV_NOT && b[0] == a) return true;
  return d_complementFacts.count({a, b}) > 0;
}

Node PbvMw::dropDisjoint(TNode m, TNode t)
{
  Kind k = t.getKind();
  if (k != Kind::PBV_XOR && k != Kind::PBV_OR) return t;
  // under the mask m, an operand q with m & q = 0 contributes nothing
  std::vector<Node> kids;
  for (const Node& c : t)
  {
    if (!areDisjoint(m, c)) kids.push_back(dropDisjoint(m, c));
  }
  if (kids.size() == t.getNumChildren()) return t;
  if (kids.empty())
  {
    return nodeManager()->mkNode(
        Kind::INT_TO_PBV, widthTerm(t), nodeManager()->mkConstInt(Rational(0)));
  }
  return kids.size() == 1 ? kids[0] : acNormBitwise(nodeManager()->mkNode(k, kids));
}

Node PbvMw::acNormBitwise(Node n)
{
  Kind k = n.getKind();
  if (k != Kind::PBV_AND && k != Kind::PBV_OR && k != Kind::PBV_XOR) return n;
  NodeManager* nm = nodeManager();
  std::vector<Node> flat;
  std::vector<Node> work(n.begin(), n.end());
  while (!work.empty())
  {
    Node c = work.back();
    work.pop_back();
    if (c.getKind() == k)
    {
      work.insert(work.end(), c.begin(), c.end());
    }
    else
    {
      flat.push_back(c);
    }
  }
  std::sort(flat.begin(), flat.end());
  std::vector<Node> kids;
  bool ones = false;  // xor: an odd number of all-ones operands
  for (size_t i = 0; i < flat.size(); ++i)
  {
    const Node& c = flat[i];
    if (isZero(c))
    {
      if (k == Kind::PBV_AND) return c;
      continue;
    }
    if (isOnes(c))
    {
      if (k == Kind::PBV_OR) return c;
      if (k == Kind::PBV_XOR) ones = !ones;
      continue;
    }
    if (k == Kind::PBV_XOR && i + 1 < flat.size() && flat[i + 1] == c)
    {
      ++i;  // x ^ x = 0
      continue;
    }
    if (k != Kind::PBV_XOR && !kids.empty() && kids.back() == c) continue;
    kids.push_back(c);
  }
  Node w = widthTerm(n);
  Node zero = nm->mkNode(Kind::INT_TO_PBV, w, nm->mkConstInt(Rational(0)));
  Node res;
  if (kids.empty())
  {
    res = k == Kind::PBV_AND ? nm->mkNode(Kind::PBV_NOT, zero) : zero;
  }
  else
  {
    // rebuilt as a left-nested BINARY chain: the generated --pbv-rw-mw rules
    // read node[0] and node[1] without checking the arity, so an n-ary
    // pbvand would lose its third operand to e.g. pbv-c26-and-one
    res = kids[0];
    for (size_t i = 1; i < kids.size(); ++i)
    {
      res = nm->mkNode(k, res, kids[i]);
    }
  }
  if (ones) res = nm->mkNode(Kind::PBV_NOT, res);
  return res;
}

Node PbvMw::applyBitwise(Node n)
{
  const options::HolderSMT& o = options().smt;
  if (!o.pbvMwShiftBitwise && !o.pbvMwSignIdioms && !d_cond.anyBitwise())
  {
    return n;
  }
  NodeManager* nm = nodeManager();
  Kind k = n.getKind();
  Node zeroInt = nm->mkConstInt(Rational(0));
  auto zeroOf = [&](TNode t) {
    return nm->mkNode(Kind::INT_TO_PBV, widthTerm(t), zeroInt);
  };
  auto isBitwise = [](Kind kk) {
    return kk == Kind::PBV_AND || kk == Kind::PBV_OR || kk == Kind::PBV_XOR;
  };
  auto isShiftK = [](Kind kk) {
    return kk == Kind::PBV_SHL || kk == Kind::PBV_LSHR || kk == Kind::PBV_ASHR;
  };

  if (o.pbvMwShiftBitwise && o.pbvMwShiftBitwiseW1)
  {
    // W1: a shift distributes over and/or/xor (ashr also over not)
    if (isShiftK(k) && n.getNumChildren() == 2 && isBitwise(n[0].getKind()))
    {
      std::vector<Node> kids;
      for (const Node& c : n[0])
      {
        kids.push_back(rewriteRec(nm->mkNode(k, c, n[1])));
      }
      bump("W1");
      return acNormBitwise(nm->mkNode(n[0].getKind(), kids));
    }
    if (k == Kind::PBV_ASHR && n[0].getKind() == Kind::PBV_NOT)
    {
      bump("W1");
      return nm->mkNode(Kind::PBV_NOT, rewriteRec(nm->mkNode(k, n[0][0], n[1])));
    }
  }
  // W2, W4, W3 (conditional, learned-rewrite-pbv): shift pairs and bitwise
  // operators, ahead of the W5 normalization as always.
  {
    Node r = lrShiftBitwise(n);
    if (r != n)
    {
      return r;
    }
  }
  if (o.pbvMwShiftBitwise)
  {
    // W5
    if (isBitwise(k))
    {
      Node r = acNormBitwise(n);
      if (r != n)
      {
        bump("W5");
        return r;
      }
    }
  }

  // G2a, G4 (conditional, learned-rewrite-pbv): sgt/sge and bitwise
  // operators, which no unconditional G rule matches.
  {
    Node r = lrSignIdioms(n);
    if (r != n)
    {
      return r;
    }
  }
  if (o.pbvMwSignIdioms)
  {
    // G1: (x & msbmask) = 0  ->  ~(x <s 0)
    if (k == Kind::EQUAL && n[0].getType().isPbv())
    {
      for (size_t s = 0; s < 2; ++s)
      {
        TNode a = n[s], z = n[1 - s];
        if (!isZero(z) || a.getKind() != Kind::PBV_AND || a.getNumChildren() != 2)
        {
          continue;
        }
        for (size_t j = 0; j < 2; ++j)
        {
          if (isMsbMask(a[j]))
          {
            bump("G1");
            return nm->mkNode(Kind::PBV_SLT, a[1 - j], z).notNode();
          }
        }
      }
    }
    // G2 (sgt/sge against 0 / -1, conditional): in lrSignIdioms above
    if (k == Kind::PBV_SLT && isOnes(n[0]))
    {
      bump("G2");
      return nm->mkNode(Kind::PBV_SLT, n[1], zeroOf(n[1])).notNode();
    }
    if (k == Kind::PBV_SLE && isZero(n[0]))
    {
      bump("G2");
      return nm->mkNode(Kind::PBV_SLT, n[1], n[0]).notNode();
    }
    if (k == Kind::PBV_SLE && isOnes(n[1]))
    {
      bump("G2");
      return nm->mkNode(Kind::PBV_SLT, n[0], zeroOf(n[0]));
    }
    // G3: m >>s (w-1) is the sign of m in every bit
    if (k == Kind::PBV_ASHR && !widthMinusOne(n[1]).isNull())
    {
      Node z = zeroOf(n);
      bump("G3");
      return nm->mkNode(Kind::ITE,
                        nm->mkNode(Kind::PBV_SLT, n[0], z),
                        nm->mkNode(Kind::PBV_NOT, z),
                        z);
    }
    // G4 (conditional): in lrSignIdioms above
    // G6
    if (k == Kind::ITE && n[0].getKind() == Kind::NOT)
    {
      bump("G6");
      return nm->mkNode(Kind::ITE, n[0][0], n[2], n[1]);
    }
  }

  // G5 (a, b unconditional; c conditional, learned-rewrite-pbv). On a binary
  // pbvadd, which no other G rule matches.
  if (k == Kind::PBV_ADD && n.getNumChildren() == 2)
  {
    for (size_t i = 0; i < 2; ++i)
    {
      TNode x = n[i], z = n[1 - i];
      if (o.pbvMwSignIdioms)
      {
        if (x.getKind() == Kind::PBV_SUB && x.getNumChildren() == 2
            && x[1] == z)
        {
          bump("G5");
          return x[0];
        }
        if (isZero(x))
        {
          bump("G5");
          return z;
        }
      }
      Node r = lrSignIdiomsAddIte(n, i);
      if (r != n)
      {
        return r;
      }
    }
  }

  // K4 (conditional, learned-rewrite-pbv)
  {
    Node r = lrSubsetFacts(n);
    if (r != n)
    {
      return r;
    }
  }
  // K1, K2, K3 (conditional, learned-rewrite-pbv)
  return lrMaskFacts(n);
}

Node PbvMw::rewriteRec(TNode n)
{
  auto it = d_cache.find(n);
  if (it != d_cache.end())
  {
    return it->second;
  }
  Node res;
  if (n.getNumChildren() == 0 || n.isClosure())
  {
    res = n;
  }
  else
  {
    std::vector<Node> kids;
    kids.reserve(n.getNumChildren());
    bool changed = false;
    for (const Node& c : n)
    {
      Node nc = rewriteRec(c);
      changed = changed || (nc != c);
      kids.push_back(nc);
    }
    Node cur = Node(n);
    if (changed)
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
      cur = nb.constructNode();
    }
    // Re-apply until a fixed point: A can fire on what B just produced.
    Node prev;
    do
    {
      prev = cur;
      cur = applyRules(cur);
    } while (cur != prev);
    res = cur;
  }
  d_cache[n] = res;
  return res;
}

PreprocessingPassResult PbvMw::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  std::vector<Node> all;
  all.reserve(assertionsToPreprocess->size());
  for (size_t i = 0, sz = assertionsToPreprocess->size(); i < sz; ++i)
  {
    all.push_back((*assertionsToPreprocess)[i]);
  }
  harvestWidths(all);
  // For rule M3's `z <u m`; harmless when --pbv-mask-slice is off.
  harvestUltBounds(all);
  // The extension-normalization rules delete sub-terms, and with them the
  // admissibility constraints the int-blaster would state for them. Assert
  // Adm of the input first, so it survives, and let the order facts use it.
  const options::HolderSMT& o = options().smt;
  const bool bitwise =
      o.pbvMwShiftBitwise || o.pbvMwSignIdioms || d_cond.anyBitwise();
  const size_t numOriginal = assertionsToPreprocess->size();
  if (o.pbvMwTruncPush || o.pbvMwLowMask || o.pbvMwExtBitwise
      || o.pbvMwSextBv1 || o.pbvMwSextIdioms || d_cond.d_truncPush
      || d_cond.d_extBitwise || d_cond.d_sextBv1 || d_cond.d_sextIdioms
      || d_cond.d_signedRange || bitwise || o.pbvRewritesMin)
  {
    std::vector<Node> adm;
    pinAdmissibility(all, adm);
    // learned-rewrite-pbv and pbv-mw both pin; the second finds the first's
    // constraints already asserted.
    std::unordered_set<Node> present(all.begin(), all.end());
    for (const Node& c : adm)
    {
      if (present.count(c))
      {
        continue;
      }
      assertionsToPreprocess->push_back(c, false, nullptr,
                                        TrustId::UNKNOWN_PREPROCESS_LEMMA,
                                        true);
      all.push_back(c);
    }
  }
  // The order facts behind every side condition: the assertions with the
  // pinned Adm, plus the literals non-clausal simplification has learned, if
  // it has run (it normally has not, this early).
  std::vector<Node> facts(all);
  if (d_cond.anyPbv())
  {
    std::vector<Node> ll = d_preprocContext->getLearnedLiterals();
    facts.insert(facts.end(), ll.begin(), ll.end());
  }
  d_facts.harvest(facts);
  if (bitwise)
  {
    // Width canonicalization (families W/G/K): only on the original
    // assertions -- applied to the Adm pinned above it would turn
    // `(= (pbvsize x) (pbvsize y))` into `true` and lose the constraint.
    std::vector<Node> orig(all.begin(), all.begin() + numOriginal);
    buildWidthClasses(orig);
    if (!d_widthSubst.empty())
    {
      for (size_t i = 0; i < numOriginal; ++i)
      {
        Node a = (*assertionsToPreprocess)[i];
        Node b = a.substitute(d_widthSubst.begin(), d_widthSubst.end());
        if (b != a)
        {
          assertionsToPreprocess->replace(i, rewrite(b));
        }
      }
    }
    if (d_cond.d_maskFacts || d_cond.d_maskFactsIte)
    {
      std::vector<Node> now;
      for (size_t i = 0; i < numOriginal; ++i)
      {
        now.push_back((*assertionsToPreprocess)[i]);
      }
      harvestMaskFacts(now);
    }
  }

  for (size_t i = 0, sz = assertionsToPreprocess->size(); i < sz; ++i)
  {
    Node before = (*assertionsToPreprocess)[i];
    Node after = rewriteRec(before);
    if (after != before)
    {
      assertionsToPreprocess->replace(i, after);
      assertionsToPreprocess->ensureRewritten(i);
    }
  }

  Trace("pbv-mw") << "pbv-mw: width links=" << d_sizeAlias.size();
  for (const auto& [r, c] : d_fired)
  {
    Trace("pbv-mw") << "  " << r << "=" << c;
  }
  Trace("pbv-mw") << std::endl;
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
