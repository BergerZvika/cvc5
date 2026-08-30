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
 * THE RULES  (all gated by --pbv-preprocess-mw)
 * ===========================================================================
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
 */

#include "preprocessing/passes/pbv_mw.h"

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

/* == rewriting ============================================================= */

Node PbvMw::applyRules(Node n)
{
  NodeManager* nm = nodeManager();
  Node one = nm->mkConstInt(Rational(1));
  Kind k = n.getKind();

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

  // --- F : pull a shl out from under a matching lshr  (--pbv-shift-add-distrib)
  //
  //   ((x << c) + y) >> c   ->   x + (y >> c)
  //
  // parabit's div_mult_self, (x + y*z) div y = (x div y) + z, applied at the PBV
  // level -- the only place left, since the int-blaster purifies its divisions
  // into skolems while translating and no integer-level rule can see the pattern
  // afterwards. Every operand of a multi-width goal carries zero extensions, so
  // both the addends and the two shift amounts are compared with those stripped.
  //
  // Valid only when `x << c` does not overflow the width s it is computed at.
  // For a p-bit x and a u-bit shift amount c (so c <= 2^u - 1) that is
  //     s >= p + (2^u - 1)
  // which is NON-linear; it goes to the order facts, where 2^u is an opaque atom
  // and the constraint is linear in {s, p, 2^u} -- exactly the form such goals
  // state as a precondition.
  if (options().smt.pbvShiftAddDistrib && k == Kind::PBV_LSHR
      && n.getNumChildren() == 2)
  {
    TNode add = stripZext(n[0]);
    TNode c2 = stripZext(n[1]);
    if (add.getKind() == Kind::PBV_ADD && add.getNumChildren() == 2)
    {
      for (size_t side = 0; side < 2; ++side)
      {
        TNode shl = stripZext(add[side]);
        TNode y = add[1 - side];
        if (shl.getKind() != Kind::PBV_SHL || shl.getNumChildren() != 2)
        {
          continue;
        }
        TNode x = stripZext(shl[0]);
        TNode c1 = stripZext(shl[1]);
        if (c1 != c2) continue;
        Node sW = widthOf(shl);
        Node pW = widthOf(x);
        Node uW = widthOf(c1);
        Node yW = widthOf(y);
        Node outW = widthOf(n);
        if (sW.isNull() || pW.isNull() || uW.isNull() || yW.isNull()
            || outW.isNull())
        {
          continue;
        }
        // s >= p + (2^u - 1).  The goal may spell 2^u either way -- (** 2 u)
        // or (int.pow2 u) -- and the order facts treat the power as an opaque
        // atom, so a fact stated with the other spelling does not match. Try
        // both before giving up.
        bool ok = false;
        for (Kind pk : {Kind::EXP, Kind::POW2})
        {
          Node pow2u = pk == Kind::EXP
                           ? nm->mkNode(pk, nm->mkConstInt(Rational(2)), uW)
                           : nm->mkNode(pk, uW);
          Node need = rewrite(
              nm->mkNode(Kind::ADD, pW, nm->mkNode(Kind::SUB, pow2u, one)));
          if (d_facts.leq(need, sW))
          {
            ok = true;
            break;
          }
        }
        if (!ok) continue;
        Node xe = nm->mkNode(Kind::PBV_ZERO_EXTEND,
                             rewrite(nm->mkNode(Kind::SUB, outW, pW)), x);
        Node ye = nm->mkNode(Kind::PBV_ZERO_EXTEND,
                             rewrite(nm->mkNode(Kind::SUB, outW, yW)),
                             stripZext(y));
        bump("F-shift-add-distrib");
        return nm->mkNode(Kind::PBV_ADD,
                          xe,
                          nm->mkNode(Kind::PBV_LSHR, ye, n[1]));
      }
    }
  }

  // --- E : sign extension over a zero extension  (--pbv-sext-to-zext) ---
  //   (psign_extend n (pzero_extend m x))  ->  (pzero_extend (n+m) x)
  //                                            side condition: m >= 1
  // A zero extension by at least one bit forces the msb of its result to 0, so
  // the enclosing sign extension pads with zeros and is a zero extension. The
  // rewriter cannot host this: without the side condition the mixed merge is
  // unsound, which is why pbv-merge-* carries only the zext/zext and sext/sext
  // forms. `m` is typically a difference like `(- w9 w4)`, positive only via an
  // asserted `(> w9 w4)`, so the condition goes to the order facts.
  if (options().smt.pbvSextToZext && k == Kind::PBV_SIGN_EXTEND
      && n.getNumChildren() == 2 && n[1].getKind() == Kind::PBV_ZERO_EXTEND
      && n[1].getNumChildren() == 2)
  {
    Node m = n[1][0];
    if (d_facts.geqConst(m, Rational(1)))
    {
      Node sum = rewrite(nm->mkNode(Kind::ADD, n[0], m));
      bump("E-sext-over-zext");
      return nm->mkNode(Kind::PBV_ZERO_EXTEND, sum, n[1][1]);
    }
  }

  // --- E2 : sign extension of a difference of two narrower values --------
  //   (psign_extend n (pbvsub X Y))  ->  (pbvsub (pzero_extend n X)
  //                                              (pzero_extend n Y))
  //   side condition: X and Y are each a zero extension by >= 1 bit.
  //
  // Both operands then have msb 0, so at their common width W they lie in
  // [0, 2^(W-1)) and the true difference X-Y lies in (-2^(W-1), 2^(W-1)) --
  // exactly the range a signed W-bit value represents. So the W-bit wrapped
  // difference read as signed IS X-Y, and sign-extending it to W+n bits gives
  // (X-Y) mod 2^(W+n), which is what subtracting the two zero-extended
  // operands at width W+n computes. This is parabit's `signed_of_diff`.
  //
  // The point is not the subtraction but the extension: this is the shape the
  // Industry equations put under a multiplication, where psign_extend's msb
  // ITE and its two pow2 terms are what the arithmetic solver chokes on.
  if (options().smt.pbvSextToZext && k == Kind::PBV_SIGN_EXTEND
      && n.getNumChildren() == 2 && n[1].getKind() == Kind::PBV_SUB
      && n[1].getNumChildren() == 2)
  {
    TNode X = n[1][0];
    TNode Y = n[1][1];
    auto msbZero = [&](TNode t) {
      return t.getKind() == Kind::PBV_ZERO_EXTEND && t.getNumChildren() == 2
             && d_facts.geqConst(t[0], Rational(1));
    };
    if (msbZero(X) && msbZero(Y))
    {
      Node xe = nm->mkNode(Kind::PBV_ZERO_EXTEND, n[0], X);
      Node ye = nm->mkNode(Kind::PBV_ZERO_EXTEND, n[0], Y);
      bump("E2-sext-of-diff");
      return nm->mkNode(Kind::PBV_SUB, xe, ye);
    }
  }

  // --- A / B : low extract  t[i:0] -------------------------------------
  if (options().smt.pbvPreprocessMw && k == Kind::PBV_EXTRACT
      && n.getNumChildren() == 3
      && n[2].isConst() && n[2].getConst<Rational>().sgn() == 0)
  {
    Node i = n[1];
    Node target = nm->mkNode(Kind::ADD, i, one);  // the extract's width
    Node child = n[0];

    // A: the extract exactly covers an extension's source.
    if (isExtend(child) && widthEq(widthOf(child[1]), target))
    {
      bump(child.getKind() == Kind::PBV_ZERO_EXTEND ? "A1-zext" : "A2-sext");
      return child[1];
    }
    // B: push through an operator when one side is such an extension.
    if (isPushOp(child.getKind()) && child.getNumChildren() == 2)
    {
      for (size_t s = 0; s < 2; ++s)
      {
        TNode e = child[s];
        TNode other = child[1 - s];
        if (!isExtend(e) || !widthEq(widthOf(e[1]), target))
        {
          continue;
        }
        Node trunc = nm->mkNode(Kind::PBV_EXTRACT, other, i, n[2]);
        bump(s == 0 ? "B1-left" : "B2-right");
        return s == 0 ? nm->mkNode(child.getKind(), e[1], trunc)
                      : nm->mkNode(child.getKind(), trunc, e[1]);
      }
    }
    return n;
  }

  return n;
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
  // For the `m >= 1` side condition of rule E; harmless when that rule is off.
  d_facts.harvest(all);

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
