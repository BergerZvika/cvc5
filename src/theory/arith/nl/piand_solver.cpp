/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of parametric integer and (PIAND) solver.
 */

#include "theory/arith/nl/piand_solver.h"

#include <sstream>

#include "expr/skolem_manager.h"
#include "options/arith_options.h"
#include "options/smt_options.h"
#include "preprocessing/passes/bv_to_int.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"
#include "util/iand.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

PIAndSolver::PIAndSolver(Env& env, InferenceManager& im, NlModel& model)
    : EnvObj(env),
      d_im(im),
      d_model(model),
      d_iandUtils(env.getNodeManager()),
      d_initRefine(userContext()),
      d_complementIntroduced(userContext()),
      d_complementPairs(userContext())
{
  NodeManager* nm = nodeManager();
  d_false = nm->mkConst(false);
  d_true = nm->mkConst(true);
  d_zero = nm->mkConstInt(Rational(0));
  d_one = nm->mkConstInt(Rational(1));
  d_two = nm->mkConstInt(Rational(2));
  // --piand-lemmas is a comma-separated list; unknown tokens were rejected
  // when the option was validated
  std::stringstream ss(options().arith.piAndLemmaMode);
  std::string tok;
  while (std::getline(ss, tok, ','))
  {
    if (tok == "all")
    {
      d_lemmas.insert(
          {"carry", "lsb", "width-monotone", "complement", "mask", "lean"});
    }
    else if (tok == "complement-both")
    {
      d_lemmas.insert({"complement", "complement-existing"});
    }
    else if (!tok.empty() && tok != "none")
    {
      d_lemmas.insert(tok);
    }
  }
}

PIAndSolver::~PIAndSolver() {}

void PIAndSolver::initLastCall(const std::vector<Node>& xts)
{
  d_piands.clear();

  Trace("piand-mv") << "PIAND terms : " << std::endl;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    if (ak != Kind::PIAND)
    {
      // don't care about other terms
      continue;
    }
    d_piands[a[0]].push_back(a);
  }
  Trace("piand") << "We have " << d_piands.size() << " PIAND bit-width."
                 << std::endl;
}

void PIAndSolver::checkInitialRefine()
{
  Trace("piand-check") << "PIAndSolver::checkInitialRefine" << std::endl;
  NodeManager* nm = nodeManager();
  for (const std::pair<const Node, std::vector<Node> >& is : d_piands)
  {
    // the reference bitwidth
    Node k = is.first;
    for (const Node& i : is.second)
    {
      Node x = i[1];
      Node y = i[2];
      if (d_initRefine.find(i) != d_initRefine.end())
      {
        // already sent initial axioms for i in this user context
        continue;
      }
      d_initRefine.insert(i);
      // Node twok = nm->mkNode(Kind::POW2, k);
      Node twok = nm->mkNode(Kind::EXP, d_two, k);
      Node arg0Mod2 = nm->mkNode(Kind::INTS_MODULUS, x, d_two);
      Node arg1Mod2 = nm->mkNode(Kind::INTS_MODULUS, y, d_two);
      Node twok_minus_one = nm->mkNode(Kind::SUB, twok, d_one);
      Node k_gt_0 = nm->mkNode(Kind::GT, k, d_zero);
      Node x_geq_zero = nm->mkNode(Kind::GEQ, x, d_zero);
      Node x_lt_pow2 = nm->mkNode(Kind::LT, x, twok);
      Node x_range = nm->mkNode(Kind::AND, x_geq_zero, x_lt_pow2);
      Node y_geq_zero = nm->mkNode(Kind::GEQ, y, d_zero);
      Node y_lt_pow2 = nm->mkNode(Kind::LT, y, twok);
      Node y_range = nm->mkNode(Kind::AND, y_geq_zero, y_lt_pow2);

      // initial refinement lemmas
      std::vector<Node> conj;

      // x is an upper bound: x > 0 && x < 2^k && y = 2^k -1 -> piand(k,x,y) = x
      Node y_modpow2_eq_max = nm->mkNode(Kind::EQUAL, y, twok_minus_one);
      Node assum_max = nm->mkNode(Kind::AND, k_gt_0, y_modpow2_eq_max, x_range);
      conj.push_back(nm->mkNode(Kind::IMPLIES, assum_max, i.eqNode(x)));

      // y is an upper bound: y > 0 && y < 2^k && x = 2^k -1 -> piand(k,x,y) = y
      Node x_modpow2_eq_max = nm->mkNode(Kind::EQUAL, x, twok_minus_one);
      Node assum_max_x =
          nm->mkNode(Kind::AND, k_gt_0, x_modpow2_eq_max, y_range);
      conj.push_back(nm->mkNode(Kind::IMPLIES, assum_max_x, i.eqNode(y)));

      // all-ones (--piand-ones-rewrite):
      //   k > 0  =>  piand(k,x,ones) = x mod 2^k
      // when ones is syntactically 2^k-1. Unconditional in x: the mod carries
      // the masking, so no range guard is needed (cf. the maxsign rewrite).
      if (options().arith.piAndOnesRewrite)
      {
        for (size_t a = 1; a < 3; a++)
        {
          if (isOnes(i[a], k))
          {
            Node other = i[3 - a];
            Node m = nm->mkNode(Kind::INTS_MODULUS_TOTAL, other, twok);
            conj.push_back(
                nm->mkNode(Kind::IMPLIES, k_gt_0, i.eqNode(m)));
            break;
          }
        }
      }

      // min-y: y = 0 -> piand(k,x,y) = 0
      Node eq_y_zero = nm->mkNode(Kind::EQUAL, y, d_zero);
      conj.push_back(nm->mkNode(Kind::IMPLIES, eq_y_zero, i.eqNode(d_zero)));

      // min-x: x = 0 -> piand(k,x,y) = 0
      Node eq_x_zero = nm->mkNode(Kind::EQUAL, x, d_zero);
      conj.push_back(nm->mkNode(Kind::IMPLIES, eq_x_zero, i.eqNode(d_zero)));

      // idempotence: k > 0 && x > 0 && x < 2^k && x = y -> piand(k,x,y) = x
      Node eq_y_x = nm->mkNode(Kind::EQUAL, y, x);
      Node assum_idempotence = nm->mkNode(Kind::AND, k_gt_0, eq_y_x, x_range);
      conj.push_back(nm->mkNode(Kind::IMPLIES, assum_idempotence, i.eqNode(x)));

      // symmetry: piand(k,x,y) = piand(k,y,x)
      Node piand_y_x = nm->mkNode(Kind::PIAND, k, y, x);
      conj.push_back(nm->mkNode(Kind::EQUAL, i, piand_y_x));

      // range1: 0 <= piand(k,x,y)
      conj.push_back(nm->mkNode(Kind::LEQ, d_zero, i));

      // range 2: 0 <= x -> piand(k,x,y) <= x
      Node i_leq_x = nm->mkNode(Kind::LEQ, i, x);
      conj.push_back(nm->mkNode(Kind::IMPLIES, x_geq_zero, i_leq_x));

      // range 3: 0 <= y -> piand(k,x,y) <= y
      Node i_leq_y = nm->mkNode(Kind::LEQ, i, y);
      conj.push_back(nm->mkNode(Kind::IMPLIES, y_geq_zero, i_leq_y));

      // non-positive bitwidth: k <= 0 -> piand(k,x, y) = 0
      Node k_le_0 = nm->mkNode(Kind::LEQ, k, d_zero);
      conj.push_back(nm->mkNode(Kind::IMPLIES, k_le_0, i.eqNode(d_zero)));

      // lsb lemma for x: x mod 2 = 0 => piand(k,x,y) % 2 = 0
      Node piand_mod_two = nm->mkNode(Kind::INTS_MODULUS, i, d_two);
      Node arg1Mod2_eq_zero = nm->mkNode(Kind::EQUAL, arg1Mod2, d_zero);
      conj.push_back(nm->mkNode(
          Kind::IMPLIES, arg1Mod2_eq_zero, piand_mod_two.eqNode(d_zero)));

      // lsb lemma for y: y mod 2 = 0 => piand(k,x,y) % 2 = 0
      Node arg0Mod2_eq_zero = nm->mkNode(Kind::EQUAL, arg0Mod2, d_zero);
      conj.push_back(nm->mkNode(
          Kind::IMPLIES, arg0Mod2_eq_zero, piand_mod_two.eqNode(d_zero)));

      // complement split (--piand-lemmas=complement):
      //   x,y in [0,2^k)  =>  piand(k,x,y) + piand(k,x,2^k-1-y) = x
      //
      // Every set bit of x meets a set bit in exactly one of y and ~y, so the
      // two conjunctions partition x between them. This is the only schema
      // that relates a piand to the piand of the COMPLEMENT of one argument,
      // and it is what a subset hypothesis reduces to: from `(~a | b) = ones`
      // the int-blaster produces piand(k,b,2^k-1-a) = b-a, and the split with
      // x:=b, y:=a then gives piand(k,a,b) = a in one step. That shape is the
      // must-be-consistent-bits predicate of the icfb benchmarks, and without
      // this lemma cvc5 cannot discharge it at symbolic width at all.
      //
      // The lemma introduces piand(k,x,2^k-1-y). Its own complement folds back
      // to piand(k,x,y), so the chain closes rather than descending; the guard
      // below makes that independent of how the rewriter normalises the
      // subtraction.
      {
        if (hasLemma("complement")
            && d_complementIntroduced.find(i) == d_complementIntroduced.end())
        {
          Node yBar = nm->mkNode(Kind::SUB, twok_minus_one, y);
          Node piandBar = nm->mkNode(Kind::PIAND, k, x, yBar);
          d_complementIntroduced.insert(piandBar);
          d_complementIntroduced.insert(rewrite(piandBar));
          // under complement-both, keep checkComplementExisting from
          // re-emitting this same split once piandBar is registered
          for (const Node& pb : {piandBar, rewrite(piandBar)})
          {
            d_complementPairs.insert(
                i < pb ? nm->mkNode(Kind::SEXPR, i, pb, x)
                       : nm->mkNode(Kind::SEXPR, pb, i, x));
          }
          conj.push_back(nm->mkNode(
              Kind::IMPLIES,
              nm->mkNode(Kind::AND, x_range, y_range),
              nm->mkNode(Kind::ADD, i, piandBar).eqNode(x)));
        }
        // --piand-lemmas=complement-sym also splits on x:
        //   x,y in [0,2^k)  =>  piand(k,x,y) + piand(k,2^k-1-x,y) = y
        if (hasLemma("complement-sym")
            && d_complementIntroduced.find(i) == d_complementIntroduced.end())
        {
          // with `complement` also selected, the split on y was just emitted
          for (size_t a = hasLemma("complement") ? 1 : 0; a < 2; a++)
          {
            // a=0: complement y, partition x; a=1: complement x, partition y
            Node keep = a == 0 ? x : y;
            Node flip = a == 0 ? y : x;
            Node flipBar = nm->mkNode(Kind::SUB, twok_minus_one, flip);
            Node piandBar = a == 0 ? nm->mkNode(Kind::PIAND, k, x, flipBar)
                                   : nm->mkNode(Kind::PIAND, k, flipBar, y);
            d_complementIntroduced.insert(piandBar);
            d_complementIntroduced.insert(rewrite(piandBar));
            conj.push_back(nm->mkNode(
                Kind::IMPLIES,
                nm->mkNode(Kind::AND, x_range, y_range),
                nm->mkNode(Kind::ADD, i, piandBar).eqNode(keep)));
          }
        }
      }

      // constant low-mask evaluation (--piand-lemmas=mask):
      //   piand(k, 2^j-1, y) = y mod 2^min(j,k)   for y >= 0, k >= 1
      //
      // The mask 2^j-1 is j low ones, so anding with it keeps exactly the low
      // min(j,k) bits of y. The rewriter cannot fold this: its constant-
      // argument rules ask for a constant k so they can compare against
      // 2^k-1, and here k is symbolic. The case that matters in practice is
      // j=1 -- `pbvand x 1` and `pbvor x 1`, i.e. bit-0 extraction, which the
      // width-parametric MUL/UDIV/UREM lemmas are full of -- where the
      // conclusion is the linear `y mod 2`.
      {
        if (hasLemma("mask"))
        {
          for (uint32_t arg = 0; arg < 2; arg++)
          {
            Node m = arg == 0 ? x : y;      // candidate mask
            Node o = arg == 0 ? y : x;      // the other argument
            if (!m.isConst())
            {
              continue;
            }
            Rational rm = m.getConst<Rational>();
            if (!rm.isIntegral() || rm.sgn() <= 0)
            {
              continue;
            }
            Integer im = rm.getNumerator();
            // m = 2^j - 1 iff m+1 is a power of two; j = log2(m+1).
            Integer mp1 = im + Integer(1);
            if (!mp1.isPow2())
            {
              continue;
            }
            // isPow2() returns the 1-based index, so j is that minus one.
            uint32_t j = mp1.isPow2() - 1;
            if (j == 0)
            {
              continue;
            }
            Node jN = nm->mkConstInt(Rational(Integer(j)));
            Node twoj = nm->mkConstInt(Rational(Integer(2).pow(j)));
            // Guarded by the full range, like the other constant-argument
            // lemmas here: outside [0, 2^k) the low-mask reading does not
            // determine piand.
            Node oRange = nm->mkNode(Kind::AND,
                                     nm->mkNode(Kind::GEQ, o, d_zero),
                                     nm->mkNode(Kind::LT, o, twok));
            Node oNonNeg = oRange;
            // wide case: k >= j, the modulus is the constant 2^j
            conj.push_back(nm->mkNode(
                Kind::IMPLIES,
                nm->mkNode(
                    Kind::AND, oNonNeg, nm->mkNode(Kind::GEQ, k, jN)),
                i.eqNode(nm->mkNode(Kind::INTS_MODULUS, o, twoj))));
            // narrow case: 1 <= k < j, the mask covers the whole width
            conj.push_back(nm->mkNode(
                Kind::IMPLIES,
                nm->mkNode(Kind::AND,
                           oNonNeg,
                           k_gt_0,
                           nm->mkNode(Kind::LT, k, jN)),
                i.eqNode(nm->mkNode(Kind::INTS_MODULUS, o, twok))));
            break;
          }
        }
      }

      // low-c-bits upper bounds (--piand-lemmas=low-c-bits):
      //   piand(k,x,y) mod 2^c <= x mod 2^c, and the same for y,
      //   for c = 1..N (N = --piand-low-c-bits)
      //
      // piand masks both arguments to their low k bits, so its low c bits are
      // a bitwise subset of the low c bits of x and of y. No guard is needed:
      // for k < c the masked x mod 2^k is at most x mod 2^c, and for k <= 0
      // piand is 0. Every modulus is a constant, so no PIAND or EXP term is
      // introduced.
      if (hasLemma("low-c-bits"))
      {
        uint64_t maxC = options().arith.piAndLowCBits;
        for (uint64_t c = 1; c <= maxC; c++)
        {
          Node twoc = nm->mkConstInt(Rational(Integer(2).pow(c)));
          Node iMod = nm->mkNode(Kind::INTS_MODULUS, i, twoc);
          conj.push_back(
              nm->mkNode(Kind::LEQ, iMod, nm->mkNode(Kind::INTS_MODULUS, x, twoc)));
          conj.push_back(
              nm->mkNode(Kind::LEQ, iMod, nm->mkNode(Kind::INTS_MODULUS, y, twoc)));
        }
      }

      // aligned operand (--piand-lemmas=align):
      //   j >= 0 /\ 0 <= x < 2^j  =>  piand(k,x,y) = 0
      // for every existing power 2^j that y is syntactically a multiple of,
      // e.g. y = (z * 2^j) mod 2^k, a shift left by j. The low j bits of y are
      // zero and x has bits only there; for j > k, y masks to 0 at width k.
      // When y is a multiple of 2^k itself, piand(k,x,y) = 0 outright.
      //
      // aligned identity (--piand-lemmas=align-id):
      //   k > 0 /\ j >= 0 /\ 0 <= x < 2^j /\ x < 2^k  =>  piand(k,x,y) = x
      // for y = (x + m) mod 2^k with m a multiple of 2^j: the low j bits of y
      // are those of x, and x has no others.
      //
      // Neither introduces a PIAND or EXP term: 2^j is a term of y.
      if (hasLemma("align") || hasLemma("align-id"))
      {
        std::map<Node, Alignment> memo;
        for (size_t arg = 0; arg < 2; arg++)
        {
          Node a = arg == 0 ? x : y;  // the operand that is bounded
          Node b = arg == 0 ? y : x;  // the operand that is aligned
          Node aNonNeg = nm->mkNode(Kind::GEQ, a, d_zero);
          if (hasLemma("align"))
          {
            Alignment al = alignedPows(b, k, memo);
            if (al.d_zero)
            {
              conj.push_back(i.eqNode(d_zero));
            }
            for (const Node& p : al.d_pows)
            {
              conj.push_back(nm->mkNode(
                  Kind::IMPLIES,
                  nm->mkNode(Kind::AND,
                             nm->mkNode(Kind::GEQ, powExponent(p), d_zero),
                             aNonNeg,
                             nm->mkNode(Kind::LT, a, p)),
                  i.eqNode(d_zero)));
            }
          }
          if (hasLemma("align-id"))
          {
            // peel purification and the reduction mod 2^k off b
            Node bb = b;
            while (true)
            {
              Node u = SkolemManager::getUnpurifiedForm(bb);
              if (u != bb)
              {
                bb = u;
                continue;
              }
              if (bb.getKind() == Kind::ITE && isPow2kIsZero(bb[0], k))
              {
                // the mod-by-zero guard of a purified mod 2^k
                bb = bb[2];
                continue;
              }
              if ((bb.getKind() == Kind::INTS_MODULUS
                   || bb.getKind() == Kind::INTS_MODULUS_TOTAL)
                  && (bb[1] == twok || bb[1] == nm->mkNode(Kind::POW2, k)))
              {
                bb = bb[0];
                continue;
              }
              break;
            }
            if (bb.getKind() != Kind::ADD)
            {
              continue;
            }
            // m is the sum of the summands other than (one occurrence of) a
            std::vector<Node> rest;
            bool found = false;
            for (const Node& c : bb)
            {
              if (!found && c == a)
              {
                found = true;
                continue;
              }
              rest.push_back(c);
            }
            if (!found || rest.empty())
            {
              continue;
            }
            Node m = rest.size() == 1 ? rest[0] : nm->mkNode(Kind::ADD, rest);
            Alignment al = alignedPows(m, k, memo);
            Node aBelowWidth = nm->mkNode(
                Kind::AND, k_gt_0, aNonNeg, nm->mkNode(Kind::LT, a, twok));
            if (al.d_zero)
            {
              conj.push_back(
                  nm->mkNode(Kind::IMPLIES, aBelowWidth, i.eqNode(a)));
            }
            for (const Node& p : al.d_pows)
            {
              conj.push_back(nm->mkNode(
                  Kind::IMPLIES,
                  nm->mkNode(Kind::AND,
                             aBelowWidth,
                             nm->mkNode(Kind::GEQ, powExponent(p), d_zero),
                             nm->mkNode(Kind::LT, a, p)),
                  i.eqNode(a)));
            }
          }
        }
      }

      // insert lemmas
      Node lem = conj.size() == 1 ? conj[0] : nm->mkNode(Kind::AND, conj);
      Trace("piand-lemma") << "PIAndSolver::Lemma: " << lem << " ; INIT_REFINE"
                           << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_PIAND_INIT_REFINE);
    }
  }
  if (hasLemma("complement-existing"))
  {
    checkComplementExisting();
  }
}

Node PIAndSolver::maskedForm(TNode a, TNode k)
{
  NodeManager* nm = nodeManager();
  Node twok = rewrite(nm->mkNode(Kind::EXP, d_two, k));
  Node pow2k = rewrite(nm->mkNode(Kind::POW2, k));
  Node cur = rewrite(a);
  // bounded: each step strips one layer
  for (size_t n = 0; n < 8; n++)
  {
    Node u = SkolemManager::getUnpurifiedForm(cur);
    if (u != cur)
    {
      cur = rewrite(u);
      continue;
    }
    Kind ck = cur.getKind();
    if ((ck == Kind::INTS_MODULUS || ck == Kind::INTS_MODULUS_TOTAL)
        && (cur[1] == twok || cur[1] == pow2k))
    {
      cur = rewrite(cur[0]);
      continue;
    }
    break;
  }
  return cur;
}

Node PIAndSolver::lowMaskPow(TNode m, TNode k)
{
  NodeManager* nm = nodeManager();
  Node p = maskedForm(nm->mkNode(Kind::ADD, maskedForm(m, k), d_one), k);
  Kind pk = p.getKind();
  if (pk == Kind::POW2
      || (pk == Kind::EXP && p[0].isConst()
          && p[0].getConst<Rational>() == Rational(2)))
  {
    return p;
  }
  return Node::null();
}

void PIAndSolver::checkSubsetExisting()
{
  // Relations between PIAND terms that are all already present; nothing new is
  // introduced. Called from full refinement, and a lemma is sent only when the
  // current model falsifies it. Arguments are matched by their
  // residue mod 2^k (maskedForm), which is all a PIAND at width k sees. Writing
  // a <= b for "a is a bitwise subset of b at width k":
  //   subset-trans: piand(k,a,b) = a /\ piand(k,b,c) = b => piand(k,a,c) = a
  //   subset-mono:  piand(k,x,x') = x => piand(k,x,y) <= piand(k,x',y)
  //   pow2-idiom:   0 < c < 2^k /\ piand(k,c,c-1) = 0
  //                   => piand(k,y,c-1) = y mod c
  // piand(k,a,b) = a puts a in [0,2^k), so the first two need no range guard.
  // pow2-idiom does need c < 2^k: piand(2,6,5) = 0 but piand(2,3,5) = 1, not
  // 3 mod 6. Under the guard c is a power of two dividing 2^k.
  NodeManager* nm = nodeManager();
  bool doTrans = hasLemma("subset-trans");
  bool doMono = hasLemma("subset-mono");
  bool doPow2 = hasLemma("pow2-idiom");
  auto emit = [&](const Node& lem, const char* name) {
    // no dedup set: a lemma the model falsifies has not taken effect, e.g.
    // one the inference manager turned into a conflict, so it must be
    // re-sent; a lemma that did take effect is satisfied by later models
    if (!modelFalsifies(lem))
    {
      return;
    }
    Trace("piand-lemma") << "PIAndSolver::Lemma: " << lem << " ; FULL_REFINE ("
                         << name << ")" << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_PIAND_INIT_REFINE);
  };
  for (const std::pair<const Node, std::vector<Node> >& is : d_piands)
  {
    Node k = is.first;
    // terms by unordered pair of masked arguments, and (term, position) by
    // masked argument
    std::map<std::pair<Node, Node>, Node> byPair;
    std::map<Node, std::vector<std::pair<Node, size_t>>> byArg;
    std::map<Node, Node> mf;
    for (const Node& p : is.second)
    {
      for (size_t j = 1; j < 3; j++)
      {
        if (mf.find(p[j]) == mf.end())
        {
          mf[p[j]] = maskedForm(p[j], k);
        }
      }
      Node a = mf[p[1]];
      Node b = mf[p[2]];
      byPair[a < b ? std::make_pair(a, b) : std::make_pair(b, a)] = p;
      byArg[a].emplace_back(p, 1);
      if (b != a)
      {
        byArg[b].emplace_back(p, 2);
      }
    }
    auto lookup = [&byPair](const Node& a, const Node& b) {
      std::map<std::pair<Node, Node>, Node>::iterator it =
          byPair.find(a < b ? std::make_pair(a, b) : std::make_pair(b, a));
      return it == byPair.end() ? Node::null() : it->second;
    };
    for (const Node& p : is.second)
    {
      for (size_t pa = 1; pa < 3; pa++)
      {
        // p = piand(k,a,b) read as the subset fact a <= b
        Node a = p[pa];
        Node b = p[3 - pa];
        Node ma = mf[a];
        Node mb = mf[b];
        if (ma == mb)
        {
          continue;
        }
        Node pSub = p.eqNode(a);
        for (const std::pair<Node, size_t>& qe : byArg[mb])
        {
          const Node& q = qe.first;
          if (q == p)
          {
            continue;
          }
          // q = piand(k,b',c) with b' = b mod 2^k
          Node bq = q[qe.second];
          Node c = q[3 - qe.second];
          Node mc = mf[c];
          if (mc == ma || mc == mb)
          {
            continue;
          }
          if (doTrans)
          {
            Node r = lookup(ma, mc);
            if (!r.isNull())
            {
              emit(nm->mkNode(Kind::IMPLIES,
                              nm->mkNode(Kind::AND, pSub, q.eqNode(bq)),
                              r.eqNode(a)),
                   "subset-trans");
            }
          }
        }
        if (doMono)
        {
          // x = a, x' = b: every piand(k,a,y) is below piand(k,b,y)
          for (const std::pair<Node, size_t>& ae : byArg[ma])
          {
            const Node& lo = ae.first;
            if (lo == p)
            {
              continue;
            }
            Node my = mf[lo[3 - ae.second]];
            if (my == ma || my == mb)
            {
              continue;
            }
            Node hi = lookup(mb, my);
            if (!hi.isNull())
            {
              emit(nm->mkNode(
                       Kind::IMPLIES, pSub, nm->mkNode(Kind::LEQ, lo, hi)),
                   "subset-mono");
            }
          }
        }
      }
      if (doPow2)
      {
        Node twok = nm->mkNode(Kind::EXP, d_two, k);
        for (size_t pa = 1; pa < 3; pa++)
        {
          // p = piand(k,c,d) with d = c-1 mod 2^k
          Node c = p[pa];
          Node d = p[3 - pa];
          Node diff = rewrite(nm->mkNode(Kind::SUB, mf[c], mf[d]));
          if (!diff.isConst() || diff.getConst<Rational>() != Rational(1))
          {
            continue;
          }
          Node md = mf[d];
          Node guard = nm->mkNode(Kind::AND,
                                  nm->mkNode(Kind::GT, c, d_zero),
                                  nm->mkNode(Kind::LT, c, twok),
                                  p.eqNode(d_zero));
          for (const std::pair<Node, size_t>& qe : byArg[md])
          {
            const Node& q = qe.first;
            if (q == p)
            {
              continue;
            }
            Node yq = q[3 - qe.second];
            emit(nm->mkNode(
                     Kind::IMPLIES,
                     guard,
                     q.eqNode(nm->mkNode(Kind::INTS_MODULUS, yq, c))),
                 "pow2-idiom");
          }
        }
      }
    }
  }
}

bool PIAndSolver::isPow2kIsZero(TNode c, TNode k)
{
  if (c.getKind() != Kind::EQUAL)
  {
    return false;
  }
  NodeManager* nm = nodeManager();
  Node twok = nm->mkNode(Kind::EXP, d_two, k);
  Node pow2k = nm->mkNode(Kind::POW2, k);
  for (size_t j = 0; j < 2; j++)
  {
    if ((c[j] == twok || c[j] == pow2k) && c[1 - j].isConst()
        && c[1 - j].getConst<Rational>().isZero())
    {
      return true;
    }
  }
  return false;
}

Node PIAndSolver::powExponent(TNode p)
{
  return p.getKind() == Kind::POW2 ? p[0] : p[1];
}

PIAndSolver::Alignment PIAndSolver::alignedPows(TNode a,
                                                TNode k,
                                                std::map<Node, Alignment>& memo)
{
  std::map<Node, Alignment>::iterator it = memo.find(a);
  if (it != memo.end())
  {
    return it->second;
  }
  // guard against cycles through purification skolems
  memo[a] = Alignment();
  NodeManager* nm = nodeManager();
  Node twok = nm->mkNode(Kind::EXP, d_two, k);
  Node pow2k = nm->mkNode(Kind::POW2, k);
  Alignment r;
  Kind ak = a.getKind();
  if (a.isConst())
  {
    r.d_zero = a.getConst<Rational>().isZero();
  }
  else if (ak == Kind::POW2
           || (ak == Kind::EXP && a[0].isConst()
               && a[0].getConst<Rational>() == Rational(2)))
  {
    r.d_pows.insert(a);
  }
  else if (ak == Kind::MULT || ak == Kind::NONLINEAR_MULT)
  {
    for (const Node& c : a)
    {
      Alignment ac = alignedPows(c, k, memo);
      r.d_zero = r.d_zero || ac.d_zero;
      r.d_pows.insert(ac.d_pows.begin(), ac.d_pows.end());
    }
  }
  else if (ak == Kind::ADD || ak == Kind::SUB || ak == Kind::ITE)
  {
    // every summand (both ITE branches) must be aligned; a summand that is 0
    // mod 2^k constrains nothing
    bool first = true;
    r.d_zero = true;
    for (size_t j = ak == Kind::ITE ? 1 : 0; j < a.getNumChildren(); j++)
    {
      if (j == 1 && isPow2kIsZero(a[0], k))
      {
        // the mod-by-zero branch of a purified mod 2^k: 2^k = 0 only for
        // k < 0, where every PIAND at width k is 0 anyway
        continue;
      }
      Alignment ac = alignedPows(a[j], k, memo);
      if (ac.d_zero)
      {
        continue;
      }
      if (first)
      {
        r.d_pows = ac.d_pows;
        first = false;
      }
      else
      {
        std::set<Node> both;
        for (const Node& p : r.d_pows)
        {
          if (ac.d_pows.count(p))
          {
            both.insert(p);
          }
        }
        r.d_pows = both;
      }
      r.d_zero = false;
    }
  }
  else if (ak == Kind::NEG)
  {
    r = alignedPows(a[0], k, memo);
  }
  else if ((ak == Kind::INTS_MODULUS || ak == Kind::INTS_MODULUS_TOTAL)
           && (a[1] == twok || a[1] == pow2k))
  {
    r = alignedPows(a[0], k, memo);
  }
  else if (ak == Kind::PIAND && a[0] == k)
  {
    for (size_t j = 1; j < 3; j++)
    {
      Alignment ac = alignedPows(a[j], k, memo);
      r.d_zero = r.d_zero || ac.d_zero;
      r.d_pows.insert(ac.d_pows.begin(), ac.d_pows.end());
    }
  }
  else
  {
    Node u = SkolemManager::getUnpurifiedForm(a);
    if (u != a)
    {
      r = alignedPows(u, k, memo);
    }
  }
  // a multiple of 2^k masks to 0 at width k
  if (r.d_pows.count(twok) || r.d_pows.count(pow2k))
  {
    r.d_zero = true;
  }
  if (r.d_zero)
  {
    r.d_pows.clear();
  }
  memo[a] = r;
  return r;
}

bool PIAndSolver::isOnes(TNode a, TNode k)
{
  NodeManager* nm = nodeManager();
  Node twok = nm->mkNode(Kind::EXP, d_two, k);
  Node pow2k = nm->mkNode(Kind::POW2, k);
  Node ra = rewrite(a);
  for (const Node& p : {twok, pow2k})
  {
    Node ones = rewrite(nm->mkNode(Kind::SUB, p, d_one));
    if (ra == ones)
    {
      return true;
    }
    Node diff = rewrite(nm->mkNode(Kind::SUB, ra, ones));
    if (diff.isConst() && diff.getConst<Rational>().isZero())
    {
      return true;
    }
  }
  // (-1 mod 2^k) and (ones mod 2^k)
  if ((ra.getKind() == Kind::INTS_MODULUS_TOTAL
       || ra.getKind() == Kind::INTS_MODULUS)
      && (ra[1] == rewrite(twok) || ra[1] == rewrite(pow2k)))
  {
    Node b = rewrite(ra[0]);
    if (b.isConst() && b.getConst<Rational>() == Rational(-1))
    {
      return true;
    }
    return isOnes(b, k);
  }
  return false;
}

void PIAndSolver::checkComplementExisting()
{
  // The split of --piand-lemmas=complement, but only between two PIAND terms
  // that are both already present:
  //   x,y in [0,2^k)  =>  piand(k,x,y) + piand(k,x,2^k-1-y) = x
  // (and the same splitting on x). Nothing new is introduced, so this runs on
  // every call rather than once per term: a partner may only show up later.
  NodeManager* nm = nodeManager();
  for (const std::pair<const Node, std::vector<Node> >& is : d_piands)
  {
    Node k = is.first;
    // existing terms of this width, up to rewriting
    std::map<Node, Node> present;
    for (const Node& p : is.second)
    {
      present[p] = p;
      present[rewrite(p)] = p;
    }
    Node twok = nm->mkNode(Kind::EXP, d_two, k);
    Node twok_minus_one = nm->mkNode(Kind::SUB, twok, d_one);
    for (const Node& i : is.second)
    {
      for (uint32_t arg = 1; arg <= 2; arg++)
      {
        // the shared argument s stays, the other argument o is complemented
        Node s = i[3 - arg];
        Node o = i[arg];
        Node oBar = nm->mkNode(Kind::SUB, twok_minus_one, o);
        Node partner;
        for (const Node& cand : {nm->mkNode(Kind::PIAND, k, s, oBar),
                                 nm->mkNode(Kind::PIAND, k, oBar, s)})
        {
          std::map<Node, Node>::iterator it = present.find(rewrite(cand));
          if (it != present.end())
          {
            partner = it->second;
            break;
          }
        }
        if (partner.isNull() || partner == i)
        {
          continue;
        }
        Node key = i < partner ? nm->mkNode(Kind::SEXPR, i, partner, s)
                               : nm->mkNode(Kind::SEXPR, partner, i, s);
        if (d_complementPairs.find(key) != d_complementPairs.end())
        {
          continue;
        }
        d_complementPairs.insert(key);
        Node sRange = nm->mkNode(Kind::AND,
                                 nm->mkNode(Kind::GEQ, s, d_zero),
                                 nm->mkNode(Kind::LT, s, twok));
        Node oRange = nm->mkNode(Kind::AND,
                                 nm->mkNode(Kind::GEQ, o, d_zero),
                                 nm->mkNode(Kind::LT, o, twok));
        Node lem = nm->mkNode(
            Kind::IMPLIES,
            nm->mkNode(Kind::AND, sRange, oRange),
            nm->mkNode(Kind::ADD, i, partner).eqNode(s));
        Trace("piand-lemma") << "PIAndSolver::Lemma: " << lem
                             << " ; INIT_REFINE (complement-existing)"
                             << std::endl;
        d_im.addPendingLemma(lem, InferenceId::ARITH_NL_PIAND_INIT_REFINE);
      }
    }
  }
}

void PIAndSolver::checkFullRefine()
{
  NodeManager* nm = nodeManager();
  Trace("piand-check") << "PIAndSolver::checkFullRefine";
  for (const std::pair<const Node, std::vector<Node> >& is : d_piands)
  {
    int index = 0;
    for (const Node& i : is.second)
    {
      index++;
      Node valAndXY = d_model.computeAbstractModelValue(i);
      Node valAndXYC = d_model.computeConcreteModelValue(i);
      valAndXYC = rewrite(valAndXYC);

      Node k = i[0];
      Node x = i[1];
      Node y = i[2];
      Node valK = d_model.computeConcreteModelValue(k);
      Node valX = d_model.computeConcreteModelValue(x);
      Node valY = d_model.computeConcreteModelValue(y);

      // model-based refinement needs concrete constants; if any value did
      // not reduce to a constant (e.g. huge bit-widths that the rewriter
      // and evaluator decline to materialize), we cannot check this piand
      // and must skip it
      if (!valAndXYC.isConst() || !valK.isConst() || !valX.isConst()
          || !valY.isConst())
      {
        continue;
      }

      Integer model_piand = valAndXYC.getConst<Rational>().getNumerator();
      Integer model_k = valK.getConst<Rational>().getNumerator();
      Integer model_x = valX.getConst<Rational>().getNumerator();
      Integer model_y = valY.getConst<Rational>().getNumerator();

      if (TraceIsOn("piand-check"))
      {
        Trace("piand-check")
            << "* " << i << ", value = " << valAndXY << std::endl;
        Trace("piand-check") << "  actual (" << valX << ", " << valY
                             << ") = " << valAndXYC << std::endl;
      }
      if (valAndXY == valAndXYC)
      {
        Trace("piand-check") << "...already correct" << std::endl;
        continue;
      }

      Integer ione = 1;
      Integer itwo = 2;
      Integer ipow2 = itwo.pow(model_k.getLong());
      Integer max_int = ipow2 - 1;
      Node k_gt_0 = nm->mkNode(Kind::GT, k, d_zero);
      // Node twok = nm->mkNode(Kind::POW2, k);
      Node twok = nm->mkNode(Kind::EXP, d_two, k);
      Node arg0Mod = nm->mkNode(Kind::INTS_MODULUS, x, twok);
      Node arg1Mod = nm->mkNode(Kind::INTS_MODULUS, y, twok);
      Node arg0Mod2 = nm->mkNode(Kind::INTS_MODULUS, x, d_two);
      Node arg1Mod2 = nm->mkNode(Kind::INTS_MODULUS, y, d_two);

      // base case: piand(k,1,1) = 1
      if (model_k > 0 && model_x == 1 && model_y == 1 && model_piand != 1)
      {
        Node x_equal_one = nm->mkNode(Kind::EQUAL, x, d_one);
        Node y_equal_one = nm->mkNode(Kind::EQUAL, y, d_one);
        Node assum = nm->mkNode(Kind::AND, k_gt_0, x_equal_one, y_equal_one);
        Node piand_one = nm->mkNode(Kind::EQUAL, i, d_one);
        Node xy_one_lem = nm->mkNode(Kind::IMPLIES, assum, piand_one);
        d_im.addPendingLemma(xy_one_lem,
                             InferenceId::ARITH_NL_PIAND_BASE_CASE_REFINE,
                             nullptr,
                             true);
      }

      Node x_geq_zero = nm->mkNode(Kind::GEQ, x, d_zero);
      Node x_lt_pow2 = nm->mkNode(Kind::LT, x, twok);
      Node x_range = nm->mkNode(Kind::AND, x_geq_zero, x_lt_pow2);
      Node y_geq_zero = nm->mkNode(Kind::GEQ, y, d_zero);
      Node y_lt_pow2 = nm->mkNode(Kind::LT, y, twok);
      Node y_range = nm->mkNode(Kind::AND, y_geq_zero, y_lt_pow2);

      // ----------------------------------------------------------------------
      // Flag-gated refinement lemmas (--piand-lemmas=LIST and the
      // --piand-lean-refine bool). Emitted lazily HERE in full-refine rather
      // than eagerly in checkInitialRefine: each schema fires only when the
      // current (already-wrong) model value of piand actually violates it.
      // ipow2 = 2^model_k and model_k are constants checked above.
      bool wantLean = options().arith.piAndLeanRefine || hasLemma("lean");
      Integer xModPow2 = model_k > 0 ? model_x.modByPow2(model_k.getUnsignedLong())
                                     : Integer(0);
      Integer yModPow2 = model_k > 0 ? model_y.modByPow2(model_k.getUnsignedLong())
                                     : Integer(0);

      // CARRY: k>0 /\ x,y in [0,2^k) => 2*piand(k,x,y) <= x+y.
      if (hasLemma("carry")
          && model_k > 0 && model_x >= 0 && model_x < ipow2 && model_y >= 0
          && model_y < ipow2 && itwo * model_piand > model_x + model_y)
      {
        Node two_i = nm->mkNode(Kind::MULT, d_two, i);
        Node carry_bound = nm->mkNode(Kind::LEQ, two_i, nm->mkNode(Kind::ADD, x, y));
        Node carry_assum = nm->mkNode(Kind::AND, k_gt_0, x_range, y_range);
        d_im.addPendingLemma(nm->mkNode(Kind::IMPLIES, carry_assum, carry_bound),
                             InferenceId::ARITH_NL_PIAND_INIT_REFINE, nullptr,
                             true);
      }

      // LSB equivalence: k>0 => piand mod 2 = (x mod 2)*(y mod 2).
      if (hasLemma("lsb")
          && model_k > 0
          && model_piand.euclidianDivideRemainder(itwo)
                 != model_x.euclidianDivideRemainder(itwo)
                        * model_y.euclidianDivideRemainder(itwo))
      {
        Node piand_mod_two = nm->mkNode(Kind::INTS_MODULUS, i, d_two);
        Node lsb_prod = nm->mkNode(Kind::MULT, arg0Mod2, arg1Mod2);
        Node lsb_eq = nm->mkNode(Kind::EQUAL, piand_mod_two, lsb_prod);
        d_im.addPendingLemma(nm->mkNode(Kind::IMPLIES, k_gt_0, lsb_eq),
                             InferenceId::ARITH_NL_PIAND_INIT_REFINE, nullptr,
                             true);
      }

      // symbolic low mask (--piand-lemmas=mask-sym):
      //   0 <= j <= k  =>  piand(k,x,2^j-1) = x mod 2^j
      // for an argument congruent to 2^j-1 mod 2^k, with 2^j an existing
      // power term (e.g. the `(1 << t) - 1` idiom). For j <= k the mask is
      // j low ones below 2^k, and 2^j divides 2^k, so no range guard on x is
      // needed. The modulus is the power term itself: nothing is introduced.
      // Sent only when the current model falsifies it.
      if (hasLemma("mask-sym"))
      {
        for (uint32_t arg = 0; arg < 2; arg++)
        {
          Node m = arg == 0 ? x : y;
          Node o = arg == 0 ? y : x;
          Node p = lowMaskPow(m, k);
          if (p.isNull())
          {
            continue;
          }
          Node j = powExponent(p);
          Node lem = nm->mkNode(
              Kind::IMPLIES,
              nm->mkNode(Kind::AND,
                         nm->mkNode(Kind::GEQ, j, d_zero),
                         nm->mkNode(Kind::LEQ, j, k)),
              i.eqNode(nm->mkNode(Kind::INTS_MODULUS, o, p)));
          if (modelFalsifies(lem))
          {
            d_im.addPendingLemma(
                lem, InferenceId::ARITH_NL_PIAND_INIT_REFINE, nullptr, true);
          }
        }
      }

      // overlap lower bound (--piand-lemmas=overlap-lb):
      //   x,y in [0,2^k)  =>  piand(k,x,y) >= x + y - 2^k + 1
      // x + y = (x & y) + (x | y), and x | y <= 2^k - 1. Sent only when the
      // current model falsifies it.
      if (hasLemma("overlap-lb"))
      {
        Node lem = nm->mkNode(
            Kind::IMPLIES,
            nm->mkNode(Kind::AND, x_range, y_range),
            nm->mkNode(Kind::GEQ,
                       i,
                       nm->mkNode(Kind::SUB,
                                  nm->mkNode(Kind::ADD, x, y, d_one),
                                  twok)));
        if (modelFalsifies(lem))
        {
          d_im.addPendingLemma(
              lem, InferenceId::ARITH_NL_PIAND_INIT_REFINE, nullptr, true);
        }
      }

      // LEAN tight bounds (iand-style). Each conjunct guarded by its own model
      // violation, sent as one lemma when any fires.
      if (wantLean)
      {
        // arg0Mod / arg1Mod (x,y mod 2^k) are defined in the enclosing scope.
        Node k_le_0 = nm->mkNode(Kind::LEQ, k, d_zero);
        std::vector<Node> lean;
        // 0 <= piand
        if (model_piand < 0)
          lean.push_back(nm->mkNode(Kind::LEQ, d_zero, i));
        // k>0 => piand < 2^k
        if (model_k > 0 && model_piand >= ipow2)
          lean.push_back(nm->mkNode(Kind::IMPLIES, k_gt_0,
                                    nm->mkNode(Kind::LT, i, twok)));
        // k>0 => piand <= x mod 2^k
        if (model_k > 0 && model_piand > xModPow2)
          lean.push_back(nm->mkNode(Kind::IMPLIES, k_gt_0,
                                    nm->mkNode(Kind::LEQ, i, arg0Mod)));
        // k>0 => piand <= y mod 2^k
        if (model_k > 0 && model_piand > yModPow2)
          lean.push_back(nm->mkNode(Kind::IMPLIES, k_gt_0,
                                    nm->mkNode(Kind::LEQ, i, arg1Mod)));
        // x=y => piand = x mod 2^k
        if (model_k > 0 && model_x == model_y && model_piand != xModPow2)
          lean.push_back(
              nm->mkNode(Kind::IMPLIES, x.eqNode(y), i.eqNode(arg0Mod)));
        // k<=0 => piand = 0
        if (model_k <= 0 && model_piand != 0)
          lean.push_back(nm->mkNode(Kind::IMPLIES, k_le_0, i.eqNode(d_zero)));
        if (!lean.empty())
        {
          Node lem = lean.size() == 1 ? lean[0] : nm->mkNode(Kind::AND, lean);
          d_im.addPendingLemma(lem, InferenceId::ARITH_NL_PIAND_INIT_REFINE,
                               nullptr, true);
        }
      }

      int j = -1;
      for (const Node& n : is.second)
      {
        j++;
        if (j > index)
        {
          Node k2 = n[0];
          Node x2 = n[1];
          Node y2 = n[2];
          Node valK2 = d_model.computeConcreteModelValue(k2);
          Node valX2 = d_model.computeConcreteModelValue(x2);
          Node valY2 = d_model.computeConcreteModelValue(y2);
          Node valAndXYC2 = d_model.computeConcreteModelValue(n);
          if (!valAndXYC2.isConst() || !valK2.isConst() || !valX2.isConst()
              || !valY2.isConst())
          {
            continue;
          }
          Integer model_piand2 = valAndXYC2.getConst<Rational>().getNumerator();
          Integer model_k2 = valK2.getConst<Rational>().getNumerator();
          Integer model_x2 = valX2.getConst<Rational>().getNumerator();
          Integer model_y2 = valY2.getConst<Rational>().getNumerator();

          Node arg20Mod = nm->mkNode(Kind::INTS_MODULUS, x2, twok);
          Node arg21Mod = nm->mkNode(Kind::INTS_MODULUS, y2, twok);

          Node x2_geq_zero = nm->mkNode(Kind::GEQ, x2, d_zero);
          Node x2_lt_pow2 = nm->mkNode(Kind::LT, x2, twok);
          Node x2_range = nm->mkNode(Kind::AND, x2_geq_zero, x2_lt_pow2);

          // difference: x != x2 /\ y = y2 => piand(k,x,y) != x2 \/
          // piand(k,x2,y2) != x
          if (model_k > 0 && model_k == model_k2 && model_x != model_x2
              && model_y == model_y2 && model_piand == model_x2
              && model_piand2 == model_x)
          {
            Node noneqx = nm->mkNode(
                Kind::AND,
                {k.eqNode(k2), (x.eqNode(x2)).notNode(), y.eqNode(y2)});
            Node ranges_assum =
                nm->mkNode(Kind::AND, x_range, x2_range, y_range);
            Node assum_difference =
                nm->mkNode(Kind::AND, k_gt_0, noneqx, ranges_assum);
            Node difference = nm->mkNode(
                Kind::OR, {i.eqNode(x2).notNode(), n.eqNode(x).notNode()});
            Node diff_lemm =
                nm->mkNode(Kind::IMPLIES, assum_difference, difference);
            d_im.addPendingLemma(diff_lemm,
                                 InferenceId::ARITH_NL_PIAND_DIFFERENCE_REFINE,
                                 nullptr,
                                 true);
          }

          // symmetry: piand(k,x,y) = piand(k,y,x)
          if (model_k == model_k2 && model_x == model_y2 && model_x2 == model_y
              && model_piand != model_piand2)
          {
            Node assum_sym = nm->mkNode(
                Kind::AND, {k.eqNode(k2), (x.eqNode(y2)), y.eqNode(x2)});
            Node sym_lemm = nm->mkNode(Kind::IMPLIES, assum_sym, i.eqNode(n));
            d_im.addPendingLemma(sym_lemm,
                                 InferenceId::ARITH_NL_PIAND_SYMETRY_REFINE,
                                 nullptr,
                                 true);
          }

          // WIDTH_MONOTONE (gated by --piand-lemmas): same operands at two
          // different widths agree if both arguments fit in the narrower
          // width. Requires syntactic equality of operands so the lemma is
          // structurally sound under future rewrites.
          if (hasLemma("width-monotone")
              && x == x2 && y == y2 && k != k2
              && model_k > 0 && model_k2 > 0
              && model_piand != model_piand2)
          {
            Integer narrow = model_k <= model_k2 ? model_k : model_k2;
            // only fire when the model already places x, y inside the
            // narrower width — otherwise the antecedent is false and the
            // lemma carries no information.
            Integer pow2narrow = Integer(2).pow(narrow.getUnsignedLong());
            if (model_x >= 0 && model_x < pow2narrow
                && model_y >= 0 && model_y < pow2narrow)
            {
              Node kNarrow = nm->mkNode(Kind::LEQ, k, k2);
              Node kWide = nm->mkNode(Kind::LEQ, k2, k);
              Node twokN = nm->mkNode(Kind::EXP, d_two, k);
              Node twokW = nm->mkNode(Kind::EXP, d_two, k2);
              Node xrgN = nm->mkNode(
                  Kind::AND,
                  nm->mkNode(Kind::GEQ, x, d_zero),
                  nm->mkNode(Kind::LT, x, twokN));
              Node yrgN = nm->mkNode(
                  Kind::AND,
                  nm->mkNode(Kind::GEQ, y, d_zero),
                  nm->mkNode(Kind::LT, y, twokN));
              Node xrgW = nm->mkNode(
                  Kind::AND,
                  nm->mkNode(Kind::GEQ, x, d_zero),
                  nm->mkNode(Kind::LT, x, twokW));
              Node yrgW = nm->mkNode(
                  Kind::AND,
                  nm->mkNode(Kind::GEQ, y, d_zero),
                  nm->mkNode(Kind::LT, y, twokW));
              // pick the direction whose narrower side matches the model
              Node assumWM = model_k <= model_k2
                                 ? nm->mkNode(Kind::AND, kNarrow, xrgN, yrgN)
                                 : nm->mkNode(Kind::AND, kWide, xrgW, yrgW);
              Node wm_lem =
                  nm->mkNode(Kind::IMPLIES, assumWM, i.eqNode(n));
              d_im.addPendingLemma(
                  wm_lem,
                  InferenceId::ARITH_NL_PIAND_SYMETRY_REFINE,
                  nullptr,
                  true);
            }
          }
        }
      }

      // contradition: x+y mod 2^k = 2^k-1 => piand(k,x,y) = 0
      if (model_x + model_y == max_int && model_piand != 0)
      {
        Node x_plus_y = nm->mkNode(Kind::ADD, x, y);
        Node x_plus_y_mod = nm->mkNode(Kind::INTS_MODULUS, x_plus_y, twok);
        Node twok_minus_one = nm->mkNode(Kind::SUB, twok, d_one);
        Node assum = nm->mkNode(Kind::EQUAL, x_plus_y_mod, twok_minus_one);
        Node piand_zero = nm->mkNode(Kind::EQUAL, i, d_zero);
        Node neg_lem = nm->mkNode(Kind::IMPLIES, assum, piand_zero);
        d_im.addPendingLemma(neg_lem,
                             InferenceId::ARITH_NL_PIAND_CONTRADITION_REFINE,
                             nullptr,
                             true);
      }

      // one: k > 0 && y = 1 -> piand(k,x,y) = x mod 2
      if (model_k > 0 && model_y == 1 && model_piand != model_x.modByPow2(1))
      {
        Node y_equal_one = nm->mkNode(Kind::EQUAL, y, d_one);
        Node asum_lsb = nm->mkNode(Kind::AND, k_gt_0, y_equal_one);
        Node lsb = nm->mkNode(Kind::EQUAL, i, arg0Mod2);
        Node y_one_lem = nm->mkNode(Kind::IMPLIES, asum_lsb, lsb);
        d_im.addPendingLemma(
            y_one_lem, InferenceId::ARITH_NL_PIAND_ONE_REFINE, nullptr, true);
      }

      // one: k > 0 && x = 1 -> piand(k,x,y) = y mod 2
      if (model_k > 0 && model_x == 1 && model_piand != model_y.modByPow2(1))
      {
        Node x_equal_one = nm->mkNode(Kind::EQUAL, x, d_one);
        Node asum_lsb2 = nm->mkNode(Kind::AND, k_gt_0, x_equal_one);
        Node lsb2 = nm->mkNode(Kind::EQUAL, i, arg1Mod2);
        Node x_one_lem = nm->mkNode(Kind::IMPLIES, asum_lsb2, lsb2);
        d_im.addPendingLemma(
            x_one_lem, InferenceId::ARITH_NL_PIAND_ONE_REFINE, nullptr, true);
      }

      Node lem_sum = sumBasedLemma(i, Kind::GEQ);
      d_im.addPendingLemma(
          lem_sum, InferenceId::ARITH_NL_PIAND_SUM_REFINE, nullptr, true);
    }
  }
  if (hasLemma("subset-trans") || hasLemma("subset-mono")
      || hasLemma("pow2-idiom"))
  {
    checkSubsetExisting();
  }
}

bool PIAndSolver::modelFalsifies(const Node& lem)
{
  Node v = d_model.computeAbstractModelValue(lem);
  return v.isConst() && !v.getConst<bool>();
}

Node PIAndSolver::sumBasedLemma(Node i, Kind kind)
{
  Assert(i.getKind() == Kind::PIAND);
  Node k = d_model.computeConcreteModelValue(i[0]);
  Node x = i[1];
  Node y = i[2];
  uint64_t granularity = options().smt.BVAndIntegerGranularity;
  uint64_t int_k = k.getConst<Rational>().getNumerator().toUnsignedInt();
  NodeManager* nm = nodeManager();
  // (i[0] >= k /\  0 <= x < 2^k /\  0 <= y < 2^k) => i = sum
  Node width = nm->mkNode(kind, i[0], k);
  Node condition;
  Node pow2_k = nm->mkConstInt(Integer(2).pow(int_k));
  Node zero = nm->mkConstInt(Rational(0));
  Node x_pos = nm->mkNode(Kind::GEQ, x, zero);
  Node y_pos = nm->mkNode(Kind::GEQ, y, zero);
  Node x_lt_pow2 = nm->mkNode(Kind::LT, x, pow2_k);
  Node y_lt_pow2 = nm->mkNode(Kind::LT, y, pow2_k);
  Node bound_x = nm->mkNode(Kind::AND, x_lt_pow2, x_pos);
  Node bound_y = nm->mkNode(Kind::AND, y_lt_pow2, y_pos);
  condition = nm->mkNode(Kind::AND, bound_x, bound_y, width);
  Node then = nm->mkNode(
      Kind::EQUAL, i, d_iandUtils.createSumNode(x, y, int_k, granularity));
  // The range guard is required for soundness: with only k >= K, the K-bit
  // sum misses the bits of x and y at positions K..k-1 whenever the actual
  // width exceeds K. It is opt-in (--piand-sum-guard) so that the unguarded
  // historical behavior stays the default for comparison.
  Node lem = nm->mkNode(
      Kind::IMPLIES, options().arith.piandSumGuard ? condition : width, then);
  return lem;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
