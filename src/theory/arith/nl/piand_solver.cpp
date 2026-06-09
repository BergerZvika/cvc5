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
      d_initRefine(userContext())
{
  NodeManager* nm = nodeManager();
  d_false = nm->mkConst(false);
  d_true = nm->mkConst(true);
  d_zero = nm->mkConstInt(Rational(0));
  d_one = nm->mkConstInt(Rational(1));
  d_two = nm->mkConstInt(Rational(2));
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
      Node arg0Mod = nm->mkNode(Kind::INTS_MODULUS, x, twok);
      Node arg1Mod = nm->mkNode(Kind::INTS_MODULUS, y, twok);
      Node arg0Mod2 = nm->mkNode(Kind::INTS_MODULUS, x, d_two);
      Node arg1Mod2 = nm->mkNode(Kind::INTS_MODULUS, y, d_two);
      Node plus = nm->mkNode(Kind::ADD, x, y);
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

      // strict upper bound: k > 0 -> piand(k,x,y) < 2^k.
      // Mirrors the unconditional iand bound iand(x,y) < 2^k. Without it the
      // abstract piand value is unbounded above when x, y are large compound
      // sums (as after int-blasting), and branch-and-bound never stabilizes.
      // conj.push_back(
      //     nm->mkNode(Kind::IMPLIES, k_gt_0, nm->mkNode(Kind::LT, i, twok)));

      // modular upper bounds: piand(k,x,y) <= x mod 2^k and <= y mod 2^k.
      // Tighter than range2/range3 above, which bound by the raw operands;
      // x mod 2^k is always in [0, 2^k), so this is the bound that actually
      // boxes the result regardless of how large x, y are.
      // conj.push_back(nm->mkNode(Kind::LEQ, i, arg0Mod));
      // conj.push_back(nm->mkNode(Kind::LEQ, i, arg1Mod));

      // Extra initial-refine lemmas below are gated by --piand-lemmas=MODE.
      // Each schema is enabled by ALL or by its specific mode.
      options::PIAndLemmaMode plm = options().arith.piAndLemmaMode;

      // diagonal: x = y -> piand(k,x,y) = x mod 2^k. Matches the iand
      // init-refine lemma; pins the result exactly on the diagonal.
      if (plm == options::PIAndLemmaMode::ALL
          || plm == options::PIAndLemmaMode::DIAGONAL)
      {
        conj.push_back(
            nm->mkNode(Kind::IMPLIES, x.eqNode(y), i.eqNode(arg0Mod)));
      }

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

      // CARRY: k > 0 /\ x,y in [0, 2^k) => 2*piand(k,x,y) <= x + y.
      // Each bit of piand is 1 only when both x and y have a 1 there, so
      // bit-by-bit min(b_x, b_y) <= (b_x + b_y)/2; summing gives the bound.
      if (plm == options::PIAndLemmaMode::ALL
          || plm == options::PIAndLemmaMode::CARRY)
      {
        Node two_i = nm->mkNode(Kind::MULT, d_two, i);
        Node carry_bound = nm->mkNode(Kind::LEQ, two_i, plus);
        Node carry_assum = nm->mkNode(Kind::AND, k_gt_0, x_range, y_range);
        conj.push_back(nm->mkNode(Kind::IMPLIES, carry_assum, carry_bound));
      }

      // LSB equivalence: k > 0 => piand(k,x,y) mod 2 = (x mod 2)*(y mod 2).
      // Strictly stronger than the two one-sided LSB implications above; the
      // existing ones remain as cheap propagators.
      if (plm == options::PIAndLemmaMode::ALL
          || plm == options::PIAndLemmaMode::LSB)
      {
        Node lsb_prod = nm->mkNode(Kind::MULT, arg0Mod2, arg1Mod2);
        Node lsb_eq = nm->mkNode(Kind::EQUAL, piand_mod_two, lsb_prod);
        conj.push_back(nm->mkNode(Kind::IMPLIES, k_gt_0, lsb_eq));
      }

      // COMPLEMENT: k > 0 /\ x in [0, 2^k) /\ y = 2^k - 1 - x
      //             => piand(k,x,y) = 0.
      // Eager analogue of the existing checkFullRefine contradiction lemma.
      if (plm == options::PIAndLemmaMode::ALL
          || plm == options::PIAndLemmaMode::COMPLEMENT)
      {
        Node compl_rhs = nm->mkNode(Kind::SUB, twok_minus_one, x);
        Node compl_eq = nm->mkNode(Kind::EQUAL, y, compl_rhs);
        Node compl_assum = nm->mkNode(Kind::AND, k_gt_0, x_range, compl_eq);
        conj.push_back(
            nm->mkNode(Kind::IMPLIES, compl_assum, i.eqNode(d_zero)));
      }

      // insert lemmas
      Node lem = conj.size() == 1 ? conj[0] : nm->mkNode(Kind::AND, conj);
      Trace("piand-lemma") << "PIAndSolver::Lemma: " << lem << " ; INIT_REFINE"
                           << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_PIAND_INIT_REFINE);
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
          options::PIAndLemmaMode plmF = options().arith.piAndLemmaMode;
          if ((plmF == options::PIAndLemmaMode::ALL
               || plmF == options::PIAndLemmaMode::WIDTH_MONOTONE)
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
  Node lem = nm->mkNode(Kind::IMPLIES, width, then);
  return lem;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
