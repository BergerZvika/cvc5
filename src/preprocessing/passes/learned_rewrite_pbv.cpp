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
 * See learned_rewrite_pbv.h. The rule catalogue (shapes, side conditions,
 * soundness arguments) is in the header comment of pbv_mw.cpp; the bodies of
 * every CONDITIONAL rule live here, gated by --learned-rewrite-rules:
 *
 *   token               rules        side condition
 *   preprocess-mw       A1 A2 B1 B2  w(x) = i + 1
 *   sext-to-zext        E E2         zero extension by m >= 1
 *   shift-add-distrib   F            s >= p + 2^u - 1
 *   mask-slice          M2 M3        1 <= m <= w;  asserted z <u m
 *   trunc-push          T0 T1 T4 T5  w(t) = k;  k <= w(x) / w(x) <= k; ...
 *   ext-bitwise         X1 X3        w(a) = w(b) or w(a) <= w(b)
 *   sext-bv1            S1 S3        w(c) = 1
 *   sext-idioms         I3           0 <= m <= w - 1
 *   signed-range        R1 R2        m + 1 <= W, p <= m
 *   shift-bitwise       W2 W3 W4     same shift amount / extension amount
 *   sign-idioms         G2a G4 G5c   constant 0 / ones operand or branch
 *   mask-facts          K1 K2 K3     harvested low-mask / complement facts
 */

#include "preprocessing/passes/learned_rewrite_pbv.h"

#include <algorithm>

#include "expr/node_builder.h"
#include "smt/env.h"
#include "options/smt_options.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

LearnedRewritePbv::LearnedRewritePbv(PreprocessingPassContext* preprocContext)
    : PbvMw(preprocContext,
            "learned-rewrite-pbv",
            LearnedRewriteRules::fromString(
                preprocContext->getEnv().getOptions().smt.learnedRewriteRules))
{
}

/* == T : truncation push ==================================================== */

Node PbvMw::lrTruncPushFull(Node n, TNode t, Node kw)
{
  if (!d_cond.d_truncPush)
  {
    return n;
  }
  // T0: the extract keeps every bit.
  if (widthEq(widthOf(t), kw))
  {
    bump("T0-full-extract");
    return t;
  }
  return n;
}

Node PbvMw::lrTruncPushCut(Node n, TNode t, Node i, Node kw)
{
  if (!d_cond.d_truncPush)
  {
    return n;
  }
  NodeManager* nm = nodeManager();
  Kind tk = t.getKind();
  // T1: cut at an extension.
  if (isExtend(t) && t.getNumChildren() == 2)
  {
    TNode x = t[1];
    Node wx = widthOf(x);
    if (widthEq(wx, kw))
    {
      bump("T1-ext-exact");
      return x;
    }
    if (d_facts.leq(kw, wx))
    {
      bump("T1-ext-narrow");
      return mkLowExtract(x, i);
    }
    if (d_facts.leq(wx, kw))
    {
      bump("T1-ext-wide");
      return nm->mkNode(tk, rewrite(nm->mkNode(Kind::SUB, kw, wx)), x);
    }
  }
  // T4: nested low extracts.
  if (tk == Kind::PBV_EXTRACT && t.getNumChildren() == 3 && t[2].isConst()
      && t[2].getConst<Rational>().sgn() == 0)
  {
    bump("T4-extract-extract");
    return mkLowExtract(t[0], i);
  }
  // T5: under a left shift only the low k bits of the shifted value count,
  // and a sign and a zero extension agree on those.
  if (tk == Kind::PBV_SHL && t.getNumChildren() == 2
      && t[0].getKind() == Kind::PBV_SIGN_EXTEND
      && d_facts.leq(kw, widthOf(t[0][1])))
  {
    bump("T5-shl-sext-to-zext");
    Node a = nm->mkNode(Kind::PBV_ZERO_EXTEND, t[0][0], t[0][1]);
    return nm->mkNode(
        Kind::PBV_EXTRACT, nm->mkNode(Kind::PBV_SHL, a, t[1]), i, n[2]);
  }
  return n;
}

/* == X : extensions through bitwise operators =============================== */

Node PbvMw::lrExtBitwise(Node n)
{
  if (!d_cond.d_extBitwise)
  {
    return n;
  }
  NodeManager* nm = nodeManager();
  Kind k = n.getKind();
  size_t nc = n.getNumChildren();
  // --- X1 : a common extension out of a bitwise operator
  if ((k == Kind::PBV_AND || k == Kind::PBV_OR || k == Kind::PBV_XOR)
      && nc == 2 && isExtend(n[0]) && n[0].getKind() == n[1].getKind()
      && n[0].getNumChildren() == 2 && n[1].getNumChildren() == 2
      && admissible(n) && admissible(n[0]) && admissible(n[1]))
  {
    Kind ek = n[0].getKind();
    Node a = n[0][1];
    Node b = n[1][1];
    Node wa = widthOf(a);
    Node wb = widthOf(b);
    Node amt;
    if (widthEq(wa, wb))
    {
      amt = n[0][0];
    }
    else if (d_facts.leq(wa, wb))
    {
      a = rewriteRec(
          nm->mkNode(ek, rewrite(nm->mkNode(Kind::SUB, wb, wa)), a));
      amt = n[1][0];
    }
    else if (d_facts.leq(wb, wa))
    {
      b = rewriteRec(
          nm->mkNode(ek, rewrite(nm->mkNode(Kind::SUB, wa, wb)), b));
      amt = n[0][0];
    }
    if (!amt.isNull())
    {
      bump("X1-ext-out-of-bitwise");
      return nm->mkNode(ek, amt, rewriteRec(nm->mkNode(k, a, b)));
    }
  }
  // --- X3 : equality of two extensions of the same kind and width
  if (k == Kind::EQUAL && nc == 2 && isExtend(n[0])
      && n[0].getKind() == n[1].getKind() && n[0].getNumChildren() == 2
      && n[1].getNumChildren() == 2
      && widthEq(widthOf(n[0][1]), widthOf(n[1][1])) && admissible(n)
      && admissible(n[0]) && admissible(n[1]))
  {
    bump("X3-eq-strip-ext");
    return rewriteRec(nm->mkNode(Kind::EQUAL, n[0][1], n[1][1]));
  }
  return n;
}

/* == S : one-bit sign extension ============================================= */

Node PbvMw::lrSextBv1(Node n)
{
  if (!d_cond.d_sextBv1)
  {
    return n;
  }
  NodeManager* nm = nodeManager();
  Node one = nm->mkConstInt(Rational(1));
  Kind k = n.getKind();
  size_t nc = n.getNumChildren();
  // --- S1 : sign extension of a single bit
  if (k == Kind::PBV_SIGN_EXTEND && nc == 2 && widthEq(widthOf(n[1]), one))
  {
    bump("S1-sext-bv1");
    return nm->mkNode(
        Kind::PBV_NEG,
        rewriteRec(nm->mkNode(Kind::PBV_ZERO_EXTEND, n[0], n[1])));
  }
  // --- S3 : under a bitwise operator a one-bit sign extension is a mask,
  // all ones or all zeros by c, so the operator is a case split on c.
  // Children are rewritten first, so S1's form -(zext c) is matched too.
  if ((k == Kind::PBV_AND || k == Kind::PBV_OR || k == Kind::PBV_XOR)
      && nc == 2 && admissible(n))
  {
    auto bitOf = [&](TNode e) -> Node {
      if (e.getKind() == Kind::PBV_NEG
          && e[0].getKind() == Kind::PBV_ZERO_EXTEND)
      {
        e = e[0];
      }
      else if (e.getKind() != Kind::PBV_SIGN_EXTEND)
      {
        return Node::null();
      }
      if (!admissible(e) || !widthEq(widthOf(e[1]), one))
      {
        return Node::null();
      }
      return e[1];
    };
    for (size_t s = 0; s < 2; ++s)
    {
      Node c = bitOf(n[s]);
      if (c.isNull())
      {
        continue;
      }
      TNode t = n[1 - s];
      Node w = widthOf(n);
      Node isSet =
          nm->mkNode(Kind::EQUAL, c, nm->mkNode(Kind::INT_TO_PBV, one, one));
      Node zero = nm->mkNode(Kind::INT_TO_PBV, w, nm->mkConstInt(Rational(0)));
      bump("S3-bv1-mask");
      if (k == Kind::PBV_AND)
      {
        return nm->mkNode(Kind::ITE, isSet, t, zero);
      }
      if (k == Kind::PBV_OR)
      {
        return nm->mkNode(Kind::ITE, isSet, nm->mkNode(Kind::PBV_NOT, zero), t);
      }
      return nm->mkNode(
          Kind::ITE, isSet, rewriteRec(nm->mkNode(Kind::PBV_NOT, t)), t);
    }
  }
  return n;
}

/* == I : extension idioms =================================================== */

Node PbvMw::lrSextIdioms(Node n)
{
  if (!d_cond.d_sextIdioms)
  {
    return n;
  }
  NodeManager* nm = nodeManager();
  Node one = nm->mkConstInt(Rational(1));
  Kind k = n.getKind();
  size_t nc = n.getNumChildren();
  // --- I3 : the shift pair (a << m) >>s m
  if (k == Kind::PBV_ASHR && nc == 2 && n[0].getKind() == Kind::PBV_SHL
      && n[0].getNumChildren() == 2 && n[0][1] == n[1]
      && n[1].getKind() == Kind::INT_TO_PBV && n[1].getNumChildren() == 2
      && admissible(n) && admissible(n[0]) && admissible(n[1]))
  {
    TNode a = n[0][0];
    Node m = n[1][1];
    Node w = widthOf(a);
    // w - m is the width of the slice that survives; it must be >= 1.
    Node keep = rewrite(nm->mkNode(Kind::SUB, w, m));
    if (d_facts.nonNeg(m)
        && (widthPositive(keep) || d_facts.geqConst(keep, Rational(1))))
    {
      bump("I3-shl-ashr-sext");
      return nm->mkNode(Kind::PBV_SIGN_EXTEND,
                        m,
                        mkLowExtract(a, nm->mkNode(Kind::SUB, keep, one)));
    }
  }
  return n;
}

/* == R : signed range ======================================================= */

Node PbvMw::lrSignedRange(Node n)
{
  Kind k = n.getKind();
  if (!d_cond.d_signedRange || (k != Kind::PBV_SLT && k != Kind::PBV_SLE)
      || n.getNumChildren() != 2 || !admissible(n))
  {
    return n;
  }
  NodeManager* nm = nodeManager();
  Node one = nm->mkConstInt(Rational(1));
  auto onesAdmissible = [&](TNode c) {
    return c.getKind() == Kind::INT_TO_PBV ? admissible(c) : admissible(c[0]);
  };
  // Is t = (-1 << m) at a width W with m + 1 <= W, i.e. exactly -2^m?
  auto negPow2 = [&](TNode t, Node& m) {
    if (t.getKind() != Kind::PBV_SHL || t.getNumChildren() != 2
        || !isOnes(t[0]) || t[1].getKind() != Kind::INT_TO_PBV
        || t[1].getNumChildren() != 2 || !admissible(t) || !admissible(t[1])
        || !onesAdmissible(t[0]))
    {
      return false;
    }
    m = t[1][1];
    return d_facts.leq(rewrite(nm->mkNode(Kind::ADD, m, one)), widthOf(t));
  };
  // sext(x) of a p-bit x is >= -2^(p-1) > -2^m when p <= m. A width p is
  // positive, so p <= m also gives the m >= 0 that negPow2 needs.
  auto above = [&](TNode t, const Node& m) {
    if (t.getKind() != Kind::PBV_SIGN_EXTEND || t.getNumChildren() != 2
        || !admissible(t))
    {
      return false;
    }
    Node p = widthOf(t[1]);
    return d_facts.leq(p, m) && (widthPositive(p) || d_facts.nonNeg(m));
  };
  Node m;
  if (negPow2(n[0], m) && above(n[1], m))
  {
    bump("R-negpow2-below-sext");
    return nm->mkConst(true);
  }
  if (negPow2(n[1], m) && above(n[0], m))
  {
    bump("R-sext-above-negpow2");
    return nm->mkConst(false);
  }
  return n;
}

/* == W : shifts through bitwise operators =================================== */

Node PbvMw::lrShiftBitwise(Node n)
{
  if (!d_cond.d_shiftBitwise)
  {
    return n;
  }
  NodeManager* nm = nodeManager();
  Kind k = n.getKind();
  auto isBitwise = [](Kind kk) {
    return kk == Kind::PBV_AND || kk == Kind::PBV_OR || kk == Kind::PBV_XOR;
  };
  // W2: a shift and its inverse leave a mask
  if ((k == Kind::PBV_LSHR && n[0].getKind() == Kind::PBV_SHL)
      || (k == Kind::PBV_SHL && n[0].getKind() == Kind::PBV_LSHR))
  {
    if (n[0][1] == n[1])
    {
      Node zero = nm->mkNode(
          Kind::INT_TO_PBV, widthTerm(n), nm->mkConstInt(Rational(0)));
      Node ones = nm->mkNode(Kind::PBV_NOT, zero);
      bump("W2");
      return acNormBitwise(nm->mkNode(
          Kind::PBV_AND, n[0][0], rewriteRec(nm->mkNode(k, ones, n[1]))));
    }
  }
  // W4: an extension by the same amount leaves a bitwise operator
  if (isBitwise(k) && isExtend(n[0]))
  {
    bool same = true;
    for (const Node& c : n)
    {
      same = same && c.getKind() == n[0].getKind() && c[0] == n[0][0];
    }
    if (same)
    {
      std::vector<Node> inner;
      for (const Node& c : n) inner.push_back(c[1]);
      bump("W4");
      return nm->mkNode(n[0].getKind(),
                        n[0][0],
                        rewriteRec(acNormBitwise(nm->mkNode(k, inner))));
    }
  }
  // W3: (y >> c) & (ones >> c) -> y >> c, likewise <<
  if (k == Kind::PBV_AND)
  {
    // over the whole flattened conjunction: the chain is binary-nested
    std::vector<Node> kids;
    std::vector<Node> work(n.begin(), n.end());
    while (!work.empty())
    {
      Node c = work.back();
      work.pop_back();
      if (c.getKind() == Kind::PBV_AND)
      {
        work.insert(work.end(), c.begin(), c.end());
      }
      else
      {
        kids.push_back(c);
      }
    }
    for (size_t i = 0; i < kids.size(); ++i)
    {
      Kind ki = kids[i].getKind();
      if ((ki != Kind::PBV_LSHR && ki != Kind::PBV_SHL) || !isOnes(kids[i][0]))
      {
        continue;
      }
      for (size_t j = 0; j < kids.size(); ++j)
      {
        if (j != i && kids[j].getKind() == ki && kids[j][1] == kids[i][1])
        {
          kids.erase(kids.begin() + i);
          bump("W3");
          return kids.size() == 1
                     ? kids[0]
                     : rewriteRec(acNormBitwise(nm->mkNode(k, kids)));
        }
      }
    }
  }
  return n;
}

/* == G : sign idioms ======================================================== */

Node PbvMw::lrSignIdioms(Node n)
{
  if (!d_cond.d_signIdioms)
  {
    return n;
  }
  NodeManager* nm = nodeManager();
  Kind k = n.getKind();
  // G2a: comparisons with 0 and -1 as a sign test (sgt/sge read as the
  // swapped slt/sle, which the rewriter does not always do first)
  if ((k == Kind::PBV_SGT || k == Kind::PBV_SGE)
      && (isZero(n[0]) || isOnes(n[0]) || isZero(n[1]) || isOnes(n[1])))
  {
    bump("G2");
    return nm->mkNode(
        k == Kind::PBV_SGT ? Kind::PBV_SLT : Kind::PBV_SLE, n[1], n[0]);
  }
  // G4: a bitwise operator over a constant-branched ITE
  if (k == Kind::PBV_AND || k == Kind::PBV_OR || k == Kind::PBV_XOR)
  {
    for (size_t i = 0; i < n.getNumChildren(); ++i)
    {
      TNode t = n[i];
      if (t.getKind() != Kind::ITE || !(isZero(t[1]) || isOnes(t[1]))
          || !(isZero(t[2]) || isOnes(t[2])))
      {
        continue;
      }
      std::vector<Node> a, b;
      for (size_t j = 0; j < n.getNumChildren(); ++j)
      {
        a.push_back(j == i ? Node(t[1]) : n[j]);
        b.push_back(j == i ? Node(t[2]) : n[j]);
      }
      bump("G4");
      return nm->mkNode(Kind::ITE,
                        t[0],
                        rewriteRec(acNormBitwise(nm->mkNode(k, a))),
                        rewriteRec(acNormBitwise(nm->mkNode(k, b))));
    }
  }
  return n;
}

Node PbvMw::lrSignIdiomsAddIte(Node n, size_t i)
{
  if (!d_cond.d_signIdioms)
  {
    return n;
  }
  NodeManager* nm = nodeManager();
  TNode x = n[i], z = n[1 - i];
  // G5c: cancel an addition through an ITE
  if (x.getKind() == Kind::ITE)
  {
    auto helps = [&](TNode br) {
      return isZero(br)
             || (br.getKind() == Kind::PBV_SUB && br.getNumChildren() == 2
                 && br[1] == z);
    };
    if (helps(x[1]) || helps(x[2]))
    {
      bump("G5");
      return nm->mkNode(Kind::ITE,
                        x[0],
                        rewriteRec(nm->mkNode(Kind::PBV_ADD, x[1], z)),
                        rewriteRec(nm->mkNode(Kind::PBV_ADD, x[2], z)));
    }
  }
  return n;
}

/* == K : mask facts ========================================================= */

Node PbvMw::lrMaskFacts(Node n)
{
  if (!d_cond.d_maskFacts)
  {
    return n;
  }
  NodeManager* nm = nodeManager();
  Kind k = n.getKind();
  auto zeroOf = [&](TNode t) {
    return nm->mkNode(
        Kind::INT_TO_PBV, widthTerm(t), nm->mkConstInt(Rational(0)));
  };
  if (!d_lowMaskFacts.empty())
  {
    // K1: compare against a low mask as a test of the bits above it
    if ((k == Kind::PBV_ULT && d_lowMaskFacts.count(n[0]))
        || (k == Kind::PBV_ULE && d_lowMaskFacts.count(n[1])))
    {
      bool lt = k == Kind::PBV_ULT;
      Node m = lt ? n[0] : n[1];
      Node x = lt ? n[1] : n[0];
      Node above = rewriteRec(
          nm->mkNode(Kind::PBV_AND, x, nm->mkNode(Kind::PBV_NOT, m)));
      Node isZeroAbove = above.eqNode(zeroOf(m));
      bump("K1");
      return lt ? isZeroAbove.notNode() : isZeroAbove;
    }
    // K2: the low bits of a difference
    if (k == Kind::PBV_AND && n.getNumChildren() == 2)
    {
      for (size_t i = 0; i < 2; ++i)
      {
        TNode m = n[i], d = n[1 - i];
        if (!d_lowMaskFacts.count(m) || d.getKind() != Kind::PBV_SUB
            || d.getNumChildren() != 2)
        {
          continue;
        }
        auto masked = [&](TNode t) {
          return t.getKind() == Kind::PBV_AND
                 && std::find(t.begin(), t.end(), m) != t.end();
        };
        if (masked(d[0]) && masked(d[1])) continue;
        auto mask = [&](TNode t) {
          return rewriteRec(nm->mkNode(Kind::PBV_AND, m, dropDisjoint(m, t)));
        };
        bump("K2");
        return acNormBitwise(nm->mkNode(
            Kind::PBV_AND,
            m,
            nm->mkNode(Kind::PBV_SUB, mask(d[0]), mask(d[1]))));
      }
    }
  }
  // K3: ite(x & m = 0, x & m', x) -> x for complements m, m'
  if (k == Kind::ITE && n.getType().isPbv() && n[0].getKind() == Kind::EQUAL)
  {
    TNode c = n[0];
    TNode x = n[2], t = n[1];
    for (size_t s = 0; s < 2; ++s)
    {
      TNode a = c[s];
      if (!isZero(c[1 - s]) || a.getKind() != Kind::PBV_AND
          || a.getNumChildren() != 2 || t.getKind() != Kind::PBV_AND
          || t.getNumChildren() != 2)
      {
        continue;
      }
      for (size_t j = 0; j < 2; ++j)
      {
        if (a[j] != x) continue;
        TNode m = a[1 - j];
        for (size_t q = 0; q < 2; ++q)
        {
          if (t[q] == x && areComplements(m, t[1 - q]))
          {
            bump("K3");
            return x;
          }
        }
      }
    }
  }
  return n;
}

/* == F, E, E2, M2, M3, A/B ================================================== */

Node PbvMw::lrRules(Node n)
{
  NodeManager* nm = nodeManager();
  Node one = nm->mkConstInt(Rational(1));
  Kind k = n.getKind();

  // --- F : pull a shl out from under a matching lshr  (shift-add-distrib)
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
  if (d_cond.d_shiftAddDistrib && k == Kind::PBV_LSHR
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

  // --- E : sign extension over a zero extension  (sext-to-zext) ---
  //   (psign_extend n (pzero_extend m x))  ->  (pzero_extend (n+m) x)
  //                                            side condition: m >= 1
  // A zero extension by at least one bit forces the msb of its result to 0, so
  // the enclosing sign extension pads with zeros and is a zero extension. The
  // rewriter cannot host this: without the side condition the mixed merge is
  // unsound, which is why pbv-merge-* carries only the zext/zext and sext/sext
  // forms. `m` is typically a difference like `(- w9 w4)`, positive only via an
  // asserted `(> w9 w4)`, so the condition goes to the order facts.
  if (d_cond.d_sextToZext && k == Kind::PBV_SIGN_EXTEND
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
  if (d_cond.d_sextToZext && k == Kind::PBV_SIGN_EXTEND
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

  // --- M2 : symbolic low mask  (mask-slice)
  //
  //   x & ((1 << m) - 1)  ->  (pzero_extend (w - m) (pextract x (m-1) 0))
  //
  // for a w-bit x, under 1 <= m <= w. This is pbv-c26-and-one generalized from
  // the constant mask 1 to a symbolic run of m low ones. The side condition is
  // NOT decorative: for m > w the mask is all ones (the shift has overflowed)
  // and the conjunction is x, while the right-hand side would ask for a
  // negative extension.
  if (d_cond.d_maskSlice && k == Kind::PBV_AND && n.getNumChildren() == 2)
  {
    for (size_t s2 = 0; s2 < 2; ++s2)
    {
      TNode x = n[s2];
      TNode mask = n[1 - s2];
      // mask = (pbvsub (pbvshl (int_to_pbv w 1) (int_to_pbv w m))
      //                (int_to_pbv w 1))
      Node m;
      if (!isLowMask(mask, m))
      {
        continue;
      }
      Node w = widthOf(x);
      if (w.isNull() || !widthEq(widthOf(mask), w))
      {
        continue;
      }
      // 1 <= m <= w, from the order facts of the assertions.
      if (!widthPositive(m) || !d_facts.leq(m, w))
      {
        continue;
      }
      Node hi = rewrite(nm->mkNode(Kind::SUB, m, one));
      bump("M2-low-mask");
      return nm->mkNode(
          Kind::PBV_ZERO_EXTEND,
          rewrite(nm->mkNode(Kind::SUB, w, m)),
          rewriteRec(nm->mkNode(
              Kind::PBV_EXTRACT, x, hi, nm->mkConstInt(Rational(0)))));
    }
  }

  // --- M3 : push a low extract through a left shift  (mask-slice)
  //
  //   (a << z)[m-1:0]  ->  a[m-1:0] << z[m-1:0]      side condition: z <u m
  //
  // The guard is NOT optional: for z >= m the left side is 0 (every kept bit
  // was shifted past the extract), while the right side shifts by z mod 2^m,
  // which need not be >= m. `z <u m` comes from an asserted
  // `(pbvult z (int_to_pbv w m))` -- the in-range statement such goals carry
  // for every shift amount -- compared with the zero extensions stripped,
  // since a zero extension does not change the value.
  if (d_cond.d_maskSlice && k == Kind::PBV_EXTRACT && n.getNumChildren() == 3
      && n[2].isConst() && n[2].getConst<Rational>().sgn() == 0
      && n[0].getKind() == Kind::PBV_SHL && n[0].getNumChildren() == 2)
  {
    Node i = n[1];
    Node target = rewrite(nm->mkNode(Kind::ADD, i, one));  // extract width
    auto bit = d_ultBound.find(stripZext(n[0][1]));
    if (bit != d_ultBound.end() && widthEq(bit->second, target))
    {
      bump("M3-extract-through-shl");
      return nm->mkNode(
          Kind::PBV_SHL,
          rewriteRec(nm->mkNode(Kind::PBV_EXTRACT, n[0][0], i, n[2])),
          rewriteRec(nm->mkNode(Kind::PBV_EXTRACT, n[0][1], i, n[2])));
    }
  }

  // --- A / B : low extract  t[i:0]  (preprocess-mw) -----------------------
  if (d_cond.d_preprocessMw && k == Kind::PBV_EXTRACT
      && n.getNumChildren() == 3 && n[2].isConst()
      && n[2].getConst<Rational>().sgn() == 0)
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
  }
  return n;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
