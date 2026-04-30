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
 * Lazy translation pipeline (TRANS / CONV) for parametric bit-vectors.
 * See int_blaster.h for the design overview.
 */

#include "theory/pbv/int_blaster.h"

#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

#include "base/check.h"
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "expr/node_traversal.h"
#include "expr/internal_skolem_id.h"
#include "expr/skolem_manager.h"
#include "options/uf_options.h"
#include "proof/proof.h"
#include "smt/logic_exception.h"
#include "theory/pbv/theory_pbv_utils.h"
#include "theory/logic_info.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"
#include "util/pbv.h"
#include "util/iand.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory;
using namespace cvc5::internal::theory::pbv;

namespace cvc5::internal {

// ============================================================================
// Constructor / destructor
// ============================================================================

PIntBlaster::PIntBlaster(Env& env)
    : EnvObj(env),
      d_binarizeCache(userContext()),
      d_intblastCache(userContext()),
      d_chiMap(userContext()),
      d_kappaMap(userContext()),
      d_rangeAssertions(userContext()),
      d_bitwiseAssertions(userContext()),
      d_iandUtils(nodeManager()),
      d_context(userContext())
{
  d_nm = nodeManager();
  d_zero = d_nm->mkConstInt(Rational(0));
  d_one  = d_nm->mkConstInt(Rational(1));
  d_two  = d_nm->mkConstInt(Rational(2));
}

PIntBlaster::~PIntBlaster() {}

// ============================================================================
// ProofGenerator interface
// ============================================================================

std::shared_ptr<ProofNode> PIntBlaster::getProofFor(Node fact)
{
  CDProof cdp(d_env);
  cdp.addTrustedStep(fact, TrustId::INT_BLASTER, {}, {});
  return cdp.getProofFor(fact);
}

std::string PIntBlaster::identify() const { return "PIntBlaster"; }

// ============================================================================
// TRANS entry point
// ============================================================================

TrustNode PIntBlaster::trustedIntBlast(Node n,
                                       std::vector<TrustNode>& lemmas,
                                       std::map<Node, Node>& skolems)
{
  Assert(n == rewrite(n));
  Trace("pint-blaster") << "trustedIntBlast: " << n << std::endl;

  // Step 0 — pre-register bound kappas for every quantifier in n. This must
  // happen before computeKappa is invoked on any bound PBV variable;
  // otherwise the default branch in computeKappa would emit a top-level
  // skolem for it, which is wrong semantically (the width of a bound PBV
  // should be quantified together with the variable).
  registerBoundKappas(n);

  // Step 0b — build kappa equivalence classes so that all free PBV
  // variables forced to share a width by the formula structure resolve to
  // a single named kappa (k, k1, k2, …) instead of one skolem per variable.
  buildKappaUnionFind(n);

  // Step 1 — emit RANGE(n) and ADM(n) lemmas (TRANS = CONV(n ∧ RANGE ∧ ADM))
  // Both functions skip BOUND_VARIABLEs; per-quantifier guards are reattached
  // when the FORALL/EXISTS node is rebuilt in translateWithChildren.
  addRangeConstraints(n, lemmas);
  addAdmConstraints(n, lemmas);

  // Step 2 — post-order CONV traversal
  std::vector<Node> toVisit;
  toVisit.push_back(makeBinary(n));

  while (!toVisit.empty())
  {
    Node current = toVisit.back();
    uint64_t numChildren = current.getNumChildren();

    if (d_intblastCache.find(current) == d_intblastCache.end())
    {
      // First visit: mark with null, enqueue children
      d_intblastCache[current] = Node();
      for (const Node& child : current)
      {
        toVisit.push_back(makeBinary(child));
      }
      if (current.getKind() == Kind::APPLY_UF)
      {
        toVisit.push_back(current.getOperator());
      }
    }
    else if (!d_intblastCache[current].get().isNull())
    {
      // Already fully translated
      toVisit.pop_back();
    }
    else
    {
      // Back-visit: translate now that all children are done
      Node translation;
      if (numChildren == 0)
      {
        translation = translateNoChildren(current, lemmas, skolems);
      }
      else
      {
        std::vector<Node> translatedChildren;
        if (current.getKind() == Kind::APPLY_UF)
        {
          Assert(d_intblastCache.find(current.getOperator())
                 != d_intblastCache.end());
          translatedChildren.push_back(d_intblastCache[current.getOperator()]);
        }
        for (const Node& cc : current)
        {
          Node ccb = makeBinary(cc);
          Assert(d_intblastCache.find(ccb) != d_intblastCache.end());
          translatedChildren.push_back(d_intblastCache[ccb]);
        }
        translation =
            translateWithChildren(current, translatedChildren, lemmas);
      }
      Assert(!translation.isNull());
      d_intblastCache[current] = translation;
      d_intblastCache[translation] = translation;
      toVisit.pop_back();
    }
  }

  Assert(d_intblastCache.find(n) != d_intblastCache.end());
  Node res = d_intblastCache[n].get();

  // Step 3 — post-walker: prune redundant nested `mod pow2(k)` operations
  // produced by CONV (e.g. ((a mod p) + (b mod p)) mod p  =>  (a + b) mod p).
  res = reduceRedundantMods(res);

  // Step 4 — emit self-squaring lemmas for any `(= x (mod (* x x) p))`
  // syntactically present in the translated formula.
  detectSelfSquaring(res, lemmas);

  if (res == n)
  {
    return TrustNode::null();
  }
  return TrustNode::mkTrustRewrite(n, res, this);
}

// ============================================================================
// makeBinary — binarize n-ary PBV operators
// ============================================================================

Node PIntBlaster::makeBinary(Node n)
{
  if (d_binarizeCache.find(n) != d_binarizeCache.end())
  {
    return d_binarizeCache[n];
  }
  uint64_t numChildren = n.getNumChildren();
  Kind k = n.getKind();
  Node result = n;
  if (numChildren > 2
      && (k == Kind::PBV_CONCAT
          || k == Kind::PBV_ADD
          || k == Kind::PBV_MULT
          || k == Kind::PBV_AND
          || k == Kind::PBV_OR
          || k == Kind::PBV_XOR))
  {
    result = n[0];
    for (uint32_t i = 1; i < numChildren; i++)
    {
      result = d_nm->mkNode(k, result, n[i]);
    }
  }
  d_binarizeCache[n] = result;
  Trace("pint-blaster-debug") << "binarize: " << n << " => " << result
                              << std::endl;
  return result;
}

// ============================================================================
// Helper: fresh skolems for χ and κ
// ============================================================================

Node PIntBlaster::lookupChi(Node pbvVar) const
{
  auto it = d_chiMap.find(pbvVar);
  return it == d_chiMap.end() ? Node::null() : (*it).second;
}

Node PIntBlaster::lookupKappa(Node pbvVar) const
{
  auto it = d_kappaMap.find(pbvVar);
  return it == d_kappaMap.end() ? Node::null() : (*it).second;
}

Node PIntBlaster::getOrCreateChi(Node pbvVar)
{
  auto it = d_chiMap.find(pbvVar);
  if (it != d_chiMap.end())
  {
    return (*it).second;
  }
  // Name the χ skolem after the original PBV variable so it reads as
  // `pbv_<name>` in dumps. Use SKOLEM_EXACT_NAME so no `_<id>` suffix is
  // appended; uniqueness is guaranteed because the source name was unique
  // in the user's formula.
  std::stringstream ss;
  ss << "pbv_" << pbvVar;
  Node chi = NodeManager::mkDummySkolem(
      ss.str(), d_nm->integerType(), "PBV chi",
      SkolemFlags::SKOLEM_EXACT_NAME);
  d_chiMap[pbvVar] = chi;
  Trace("pint-blaster-debug") << "chi(" << pbvVar << ") = " << chi
                              << std::endl;
  return chi;
}

Node PIntBlaster::getOrCreateKappa(Node pbvVar)
{
  auto it = d_kappaMap.find(pbvVar);
  if (it != d_kappaMap.end())
  {
    return (*it).second;
  }
  Node rep = kappaFind(pbvVar);
  Node kappa;

  // Prefer an explicit width expression already present in the input
  // (e.g. the K of int_to_pbv K _) — avoids inventing a fresh skolem and
  // dodges name collisions with the user's own integer variables.
  auto eit = d_kappaClassExplicit.find(rep);
  if (eit != d_kappaClassExplicit.end())
  {
    kappa = eit->second;
  }
  else
  {
    auto cit = d_kappaClassSkolem.find(rep);
    if (cit != d_kappaClassSkolem.end())
    {
      kappa = cit->second;
    }
    else
    {
      // Allocate a fresh class name. Prefix `_` to keep the name distinct
      // from any user-declared `k` and emit `_k`, `_k1`, `_k2`, … .
      std::string name = (d_kappaClassCount == 0)
                             ? "_k"
                             : ("_k" + std::to_string(d_kappaClassCount));
      d_kappaClassCount++;
      kappa = NodeManager::mkDummySkolem(
          name, d_nm->integerType(), "PBV kappa class",
          SkolemFlags::SKOLEM_EXACT_NAME);
      d_kappaClassSkolem[rep] = kappa;
    }
  }
  d_kappaMap[pbvVar] = kappa;
  Trace("pint-blaster-debug") << "kappa(" << pbvVar << ") = " << kappa
                              << " [class rep " << rep << "]" << std::endl;
  return kappa;
}

// ============================================================================
// Kappa equivalence-class machinery (union-find)
// ============================================================================

Node PIntBlaster::kappaFind(Node t)
{
  auto it = d_kappaUnionFind.find(t);
  if (it == d_kappaUnionFind.end())
  {
    d_kappaUnionFind[t] = t;
    return t;
  }
  if (it->second == t)
  {
    return t;
  }
  Node root = kappaFind(it->second);
  d_kappaUnionFind[t] = root;
  return root;
}

void PIntBlaster::kappaUnion(Node a, Node b)
{
  Node ra = kappaFind(a);
  Node rb = kappaFind(b);
  if (ra == rb) return;
  d_kappaUnionFind[ra] = rb;
  // Migrate per-class metadata from `ra` (now a child) to `rb` (the new
  // root). Without this step, an explicit kappa recorded on `ra` becomes
  // orphaned and getOrCreateKappa allocates a fresh skolem instead.
  auto eit = d_kappaClassExplicit.find(ra);
  if (eit != d_kappaClassExplicit.end())
  {
    Node val = eit->second;
    d_kappaClassExplicit.erase(eit);
    if (d_kappaClassExplicit.find(rb) == d_kappaClassExplicit.end())
    {
      d_kappaClassExplicit[rb] = val;
    }
  }
  auto sit = d_kappaClassSkolem.find(ra);
  if (sit != d_kappaClassSkolem.end())
  {
    Node sk = sit->second;
    d_kappaClassSkolem.erase(sit);
    if (d_kappaClassSkolem.find(rb) == d_kappaClassSkolem.end())
    {
      d_kappaClassSkolem[rb] = sk;
    }
  }
}

Node PIntBlaster::kappaSource(Node t)
{
  // Reduce to the leaf whose κ equals κ(t).  Width-preserving recursive ops
  // forward to operand 0; ITE forwards to its first branch.  Structural
  // ops (concat / extract / extend / int_to_pbv) have no single witness —
  // return null so the caller skips unioning at that operand.
  // Bound PBV variables are NOT valid leaves: their kappa is also a bound
  // variable (set up by registerBoundKappas), and unioning them with free
  // variables would let a bound kappa escape its quantifier.
  while (true)
  {
    if (t.isVar() && t.getType().isPbv())
    {
      if (t.getKind() == Kind::BOUND_VARIABLE) return Node::null();
      return t;
    }
    if (t.getKind() == Kind::CONST_PBV) return t;
    Kind k = t.getKind();
    switch (k)
    {
      case Kind::PBV_NOT:
      case Kind::PBV_NEG:
      case Kind::PBV_ADD:
      case Kind::PBV_SUB:
      case Kind::PBV_MULT:
      case Kind::PBV_UDIV:
      case Kind::PBV_UREM:
      case Kind::PBV_AND:
      case Kind::PBV_OR:
      case Kind::PBV_XOR:
      case Kind::PBV_SHL:
      case Kind::PBV_LSHR:
      case Kind::PBV_ASHR:
      {
        // κ(parent) = κ(child 0); descend.
        t = t[0];
        break;
      }
      case Kind::ITE:
      {
        if (!t.getType().isPbv()) return Node::null();
        t = t[1];
        break;
      }
      default:
        // INT_TO_PBV, PBV_CONCAT, PBV_EXTRACT, PBV_*_EXTEND, …
        return Node::null();
    }
  }
}

void PIntBlaster::buildKappaUnionFind(Node n)
{
  std::unordered_set<Node> visited;
  std::vector<Node> stack{n};
  while (!stack.empty())
  {
    Node cur = stack.back();
    stack.pop_back();
    if (!visited.insert(cur).second) continue;

    Kind k = cur.getKind();

    // Equal-width binary / n-ary operators: every PBV operand has the same κ.
    if (cur.getNumChildren() >= 2 && cur[0].getType().isPbv())
    {
      bool isEqualWidth = false;
      switch (k)
      {
        case Kind::EQUAL:
        case Kind::PBV_ADD:
        case Kind::PBV_SUB:
        case Kind::PBV_MULT:
        case Kind::PBV_UDIV:
        case Kind::PBV_UREM:
        case Kind::PBV_AND:
        case Kind::PBV_OR:
        case Kind::PBV_XOR:
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
        case Kind::PBV_SGE: isEqualWidth = true; break;
        default: break;
      }
      if (isEqualWidth)
      {
        // Walk through unary/binary width-preserving PBV ops down to an
        // `int_to_pbv K _` and return its width K. Mirrors the descent in
        // kappaSource but bottoms out at int_to_pbv instead of a leaf var.
        auto explicitK = [](Node c) -> Node {
          while (true)
          {
            if (c.getKind() == Kind::INT_TO_PBV) return c[0];
            Kind kk = c.getKind();
            switch (kk)
            {
              case Kind::PBV_NOT:
              case Kind::PBV_NEG:
              case Kind::PBV_ADD:
              case Kind::PBV_SUB:
              case Kind::PBV_MULT:
              case Kind::PBV_UDIV:
              case Kind::PBV_UREM:
              case Kind::PBV_AND:
              case Kind::PBV_OR:
              case Kind::PBV_XOR:
              case Kind::PBV_SHL:
              case Kind::PBV_LSHR:
              case Kind::PBV_ASHR: c = c[0]; break;
              case Kind::ITE:
                if (!c.getType().isPbv()) return Node::null();
                c = c[1];
                break;
              default: return Node::null();
            }
          }
        };

        Node src0 = kappaSource(cur[0]);
        Node ek0 = explicitK(cur[0]);
        for (uint32_t i = 1; i < cur.getNumChildren(); i++)
        {
          if (!cur[i].getType().isPbv()) continue;
          Node srci = kappaSource(cur[i]);
          Node eki = explicitK(cur[i]);

          // Union variable-bearing operands.
          if (!src0.isNull() && !srci.isNull()) kappaUnion(src0, srci);

          // Propagate explicit width from one side to the other class.
          if (!srci.isNull() && !ek0.isNull())
          {
            Node rep = kappaFind(srci);
            if (d_kappaClassExplicit.find(rep) == d_kappaClassExplicit.end())
              d_kappaClassExplicit[rep] = ek0;
          }
          if (!src0.isNull() && !eki.isNull())
          {
            Node rep = kappaFind(src0);
            if (d_kappaClassExplicit.find(rep) == d_kappaClassExplicit.end())
              d_kappaClassExplicit[rep] = eki;
          }
        }
      }
    }

    // ITE over PBV: branches share κ.
    if (k == Kind::ITE && cur.getType().isPbv() && cur.getNumChildren() == 3)
    {
      Node sa = kappaSource(cur[1]);
      Node sb = kappaSource(cur[2]);
      if (!sa.isNull() && !sb.isNull()) kappaUnion(sa, sb);
    }

    for (const Node& c : cur)
    {
      stack.push_back(c);
    }
  }
}

// ============================================================================
// computeKappa — BW function (Algorithm 2)
// ============================================================================

Node PIntBlaster::computeKappa(Node t)
{
  // Check memoization cache
  auto it = d_kappaMap.find(t);
  if (it != d_kappaMap.end())
  {
    return (*it).second;
  }

  Node result;
  Kind k = t.getKind();

  switch (k)
  {
    // to-pbv(width, val): κ = the width argument (first child)
    case Kind::INT_TO_PBV:
    {
      result = t[0];
      break;
    }
    // t[i:j]: κ = i - j + 1
    case Kind::PBV_EXTRACT:
    {
      result = d_nm->mkNode(
          Kind::ADD, d_nm->mkNode(Kind::SUB, t[1], t[2]), d_one);
      break;
    }
    // zero_extend(n, t) or sign_extend(n, t): κ = κ(t) + n
    case Kind::PBV_ZERO_EXTEND:
    case Kind::PBV_SIGN_EXTEND:
    {
      result = d_nm->mkNode(Kind::ADD, computeKappa(t[1]), t[0]);
      break;
    }
    // t1 ○ t2: κ = κ(t1) + κ(t2)
    case Kind::PBV_CONCAT:
    {
      result = d_nm->mkNode(Kind::ADD, computeKappa(t[0]), computeKappa(t[1]));
      break;
    }
    // ite(cond, t2, t3): κ = κ(t2)
    case Kind::ITE:
    {
      if (t.getType().isPbv())
      {
        result = computeKappa(t[1]);
      }
      else
      {
        // Non-PBV ITE: shouldn't be asked for kappa
        Unimplemented();
      }
      break;
    }
    default:
    {
      if (t.isVar() && t.getType().isPbv())
      {
        // Free PBV variable: fresh κ skolem
        result = getOrCreateKappa(t);
      }
      else if (t.getKind() == Kind::CONST_PBV)
      {
        // Ground constant: create a fresh κ (width unknown without context)
        result = getOrCreateKappa(t);
      }
      else if (t.getNumChildren() > 0 && t.getType().isPbv())
      {
        // All other PBV operators: κ = κ(first child)
        result = computeKappa(t[0]);
      }
      else
      {
        // Should not happen for well-formed PBV terms
        Unimplemented();
      }
      break;
    }
  }

  d_kappaMap[t] = result;
  return result;
}

// ============================================================================
// mkPow2Sym / modPow2Sym / utsSym
// ============================================================================

Node PIntBlaster::mkPow2Sym(Node k)
{
  return d_nm->mkNode(Kind::EXP, d_two, k);
}

Node PIntBlaster::modPow2Sym(Node n, Node k)
{
  return d_nm->mkNode(Kind::INTS_MODULUS_TOTAL, n, mkPow2Sym(k));
}

Node PIntBlaster::utsSym(Node k, Node x)
{
  // uts(k, z) = 2 * (z mod pow2(k-1)) - z
  Node kMinus1 = d_nm->mkNode(Kind::SUB, k, d_one);
  Node modPart = modPow2Sym(x, kMinus1);
  Node twice   = d_nm->mkNode(Kind::MULT, d_two, modPart);
  return d_nm->mkNode(Kind::SUB, twice, x);
}

// Node PIntBlaster::utsSym(Node k, Node x)
// {
//   // utsSym(k, x) = x - ite(x < pow2(k-1), 0, pow2(k))
//   Node kMinus1   = d_nm->mkNode(Kind::SUB, k, d_one);
//   Node signedMin = mkPow2Sym(kMinus1);
//   // msb is zero iff x < pow2(k-1)
//   Node msbZero   = d_nm->mkNode(Kind::LT, x, signedMin);
//   Node adjust    = d_nm->mkNode(Kind::ITE, msbZero, d_zero, mkPow2Sym(k));
//   return d_nm->mkNode(Kind::SUB, x, adjust);
// }

// ============================================================================
// RANGE and ADM constraint emission
// ============================================================================

void PIntBlaster::addRangeConstraints(Node e,
                                      std::vector<TrustNode>& lemmas)
{
  // Paper "Bit-Precise Reasoning with Parametric Bit-Vectors" (SAT 2025),
  // Sec. 4: range(t, k) ::= 0 <= t < 2^k. Emitted once per free PBV variable
  // for chi(x) at width kappa(x).
  std::unordered_set<Node> visited;
  std::vector<Node> toVisit = {e};

  while (!toVisit.empty())
  {
    Node current = toVisit.back();
    toVisit.pop_back();
    if (!visited.insert(current).second) continue;

    if (current.isVar()
        && current.getType().isPbv()
        && current.getKind() != Kind::BOUND_VARIABLE)
    {
      Node chi   = getOrCreateChi(current);
      Node kappa = computeKappa(current);
      Node lowerChi = d_nm->mkNode(Kind::LEQ, d_zero, chi);
      Node upperChi = d_nm->mkNode(Kind::LT, chi, mkPow2Sym(kappa));
      Node range = d_nm->mkNode(Kind::AND, lowerChi, upperChi);
      // Rewrite first so trivially-true range constraints are filtered.
      Node simplified = rewrite(range);
      if (simplified.isConst() && simplified.getConst<bool>()) continue;
      if (!d_rangeAssertions.contains(simplified))
      {
        d_rangeAssertions.insert(simplified);
        lemmas.push_back(TrustNode::mkTrustLemma(simplified, this));
        Trace("pint-blaster") << "RANGE: " << simplified << std::endl;
      }
    }

    for (const Node& child : current)
    {
      toVisit.push_back(child);
    }
  }
}

void PIntBlaster::addAdmConstraints(Node e,
                                    std::vector<TrustNode>& lemmas)
{
  // Helper to add a lemma once. Rewrite first so admissibility constraints
  // that are now trivially true after kappa-equivalence-class allocation
  // (e.g. (= κ κ) for two PBV operands that share a class) get dropped
  // instead of being emitted as `(assert true)`.
  auto addOnce = [&](Node constr) {
    Node simplified = rewrite(constr);
    if (simplified.isConst() && simplified.getConst<bool>()) return;
    if (!d_rangeAssertions.contains(simplified))
    {
      d_rangeAssertions.insert(simplified);
      lemmas.push_back(TrustNode::mkTrustLemma(simplified, this));
      Trace("pint-blaster") << "ADM: " << simplified << std::endl;
    }
  };

  std::unordered_set<Node> visited;
  std::vector<Node> toVisit = {e};

  while (!toVisit.empty())
  {
    Node current = toVisit.back();
    toVisit.pop_back();
    if (!visited.insert(current).second) continue;

    Kind k = current.getKind();

    // Paper Fig. fig:type, function runtype:
    //   x  -> runbw(x) > 0           (bit-widths are strictly positive)
    if (current.isVar()
        && current.getType().isPbv()
        && current.getKind() != Kind::BOUND_VARIABLE)
    {
      Node kappa = computeKappa(current);
      addOnce(d_nm->mkNode(Kind::GT, kappa, d_zero));
    }

    //   int_to_pbv(k, t)  ->  k > 0
    if (k == Kind::INT_TO_PBV)
    {
      addOnce(d_nm->mkNode(Kind::GT, current[0], d_zero));
    }

    //   extract(t, i, j)  ->  0 <= j <= i < runbw(t)
    if (k == Kind::PBV_EXTRACT)
    {
      Node t = current[0];
      Node i = current[1];
      Node j = current[2];
      Node kappaT = computeKappa(t);
      addOnce(d_nm->mkNode(Kind::LEQ, d_zero, j));
      addOnce(d_nm->mkNode(Kind::LEQ, j, i));
      addOnce(d_nm->mkNode(Kind::LT, i, kappaT));
    }

    //   zero_extend(n, t) / sign_extend(n, t)  ->  n >= 0
    if (k == Kind::PBV_ZERO_EXTEND || k == Kind::PBV_SIGN_EXTEND)
    {
      addOnce(d_nm->mkNode(Kind::LEQ, d_zero, current[0]));
    }

    // Equal-width binary/n-ary PBV operators: emit κ(child_0) = κ(child_i)
    //
    // EQUAL over PBV operands must be here too: the SMT2 formula
    //   (= s (pbvnot (int_to_pbv k 0)))
    // contains two PBV-typed children whose widths must be equal.  Without
    // this constraint, κ(s) is a fresh unconstrained skolem that the solver
    // can assign independently of k, producing unsound sat witnesses.
    //
    // Note: PBV_NOT and PBV_NEG are unary (getNumChildren()==1), so the
    // ">=2" guard below means they can never fire here.  They are removed
    // from the switch to avoid misleading dead code.
    if (current.getNumChildren() >= 2)
    {
      bool isEqualWidth = false;
      switch (k)
      {
        // EQUAL over two PBV terms: both sides must have the same width.
        case Kind::EQUAL:
        // Arithmetic binary PBV operators (same-width operands):
        case Kind::PBV_ADD:
        case Kind::PBV_SUB:
        case Kind::PBV_MULT:
        case Kind::PBV_UDIV:
        case Kind::PBV_UREM:
        // Bitwise binary PBV operators:
        case Kind::PBV_AND:
        case Kind::PBV_OR:
        case Kind::PBV_XOR:
        // Shift operators (shift amount may differ in width from the value,
        // but we only constrain PBV-typed children, so the check at line
        // "if (current[i].getType().isPbv())" handles it correctly):
        case Kind::PBV_SHL:
        case Kind::PBV_LSHR:
        case Kind::PBV_ASHR:
        // Comparison operators (all require equal-width operands):
        case Kind::PBV_ULT:
        case Kind::PBV_ULE:
        case Kind::PBV_UGT:
        case Kind::PBV_UGE:
        case Kind::PBV_SLT:
        case Kind::PBV_SLE:
        case Kind::PBV_SGT:
        case Kind::PBV_SGE: isEqualWidth = true; break;
        default: break;
      }
      if (isEqualWidth && current[0].getType().isPbv())
      {
        Node k0 = computeKappa(current[0]);
        for (uint32_t i = 1; i < current.getNumChildren(); i++)
        {
          if (current[i].getType().isPbv())
          {
            Node ki = computeKappa(current[i]);
            addOnce(d_nm->mkNode(Kind::EQUAL, k0, ki));
          }
        }
      }
    }

    // ITE over PBV: κ(t2) = κ(t3)
    if (k == Kind::ITE && current.getType().isPbv()
        && current.getNumChildren() == 3)
    {
      Node k2 = computeKappa(current[1]);
      Node k3 = computeKappa(current[2]);
      addOnce(d_nm->mkNode(Kind::EQUAL, k2, k3));
    }

    for (const Node& child : current)
    {
      toVisit.push_back(child);
    }
  }
}

// ============================================================================
// registerBoundKappas — pre-pass for quantified bound PBV variables
// ============================================================================

void PIntBlaster::registerBoundKappas(Node n)
{
  std::unordered_set<Node> visited;
  std::vector<Node> stack = {n};
  while (!stack.empty())
  {
    Node cur = stack.back();
    stack.pop_back();
    if (!visited.insert(cur).second) continue;

    Kind k = cur.getKind();
    if (k == Kind::FORALL || k == Kind::EXISTS)
    {
      Node varList = cur[0];
      for (const Node& bvar : varList)
      {
        if (bvar.getType().isPbv()
            && d_kappaMap.find(bvar) == d_kappaMap.end())
        {
          std::stringstream ss;
          ss << bvar;
          Node kappa = NodeManager::mkBoundVar(ss.str() + "_kappa",
                                               d_nm->integerType());
          d_kappaMap[bvar] = kappa;
          Trace("pint-blaster")
              << "BOUND-KAPPA: " << bvar << " => " << kappa << std::endl;
        }
      }
    }
    for (const Node& child : cur)
    {
      stack.push_back(child);
    }
  }
}

// ============================================================================
// translateNoChildren — CONV for leaf nodes
// ============================================================================

Node PIntBlaster::translateNoChildren(Node original,
                                      std::vector<TrustNode>& lemmas,
                                      std::map<Node, Node>& skolems)
{
  Trace("pint-blaster-debug") << "translateNoChildren: " << original
                              << " type=" << original.getType() << std::endl;
  Node translation;

  if (original.isVar())
  {
    if (original.getType().isPbv())
    {
      if (original.getKind() == Kind::BOUND_VARIABLE)
      {
        // Bound PBV variable: create a fresh bound Int variable.
        // Range constraints are added when the enclosing quantifier is handled.
        std::stringstream ss;
        ss << original;
        translation = NodeManager::mkBoundVar(ss.str() + "_int",
                                              d_nm->integerType());
      }
      else
      {
        // Free PBV variable: CONV(x) = χ(x)
        translation = getOrCreateChi(original);
        // Record the "back-definition" for model reconstruction:
        //   x  ≈  to-pbv(κ(x), χ(x))
        Node kappa  = computeKappa(original);
        Node bvCast = d_nm->mkNode(Kind::INT_TO_PBV, kappa, translation);
        if (skolems.find(original) == skolems.end())
        {
          skolems[original] = bvCast;
        }
        else
        {
          Assert(skolems[original] == bvCast);
        }
      }
    }
    else if (original.getType().isFunction())
    {
      translation = translateFunctionSymbol(original, skolems);
    }
    else
    {
      // Integer / Boolean / other sort variable: keep as-is
      translation = original;
    }
  }
  else
  {
    // Constant or nullary operator
    if (original.getKind() == Kind::CONST_PBV)
    {
      // CONST_PBV stores a Pbv value; translate to its integer value.
      Pbv constant = original.getConst<Pbv>();
      Integer c    = constant.getValue();
      translation  = d_nm->mkConstInt(Rational(c));
    }
    else
    {
      // Integer constants, Boolean constants, etc.: unchanged.
      translation = original;
    }
  }

  Assert(!translation.isNull());
  Trace("pint-blaster-debug") << "  => " << translation << std::endl;
  return translation;
}

// ============================================================================
// translateWithChildren — CONV per Algorithm 3
// ============================================================================

Node PIntBlaster::translateWithChildren(
    Node original,
    const std::vector<Node>& translated_children,
    std::vector<TrustNode>& lemmas)
{
  Kind oldKind = original.getKind();

  if (childrenTypesChanged(original) && logicInfo().isHigherOrder())
  {
    throw LogicException("pbv-to-int does not support higher order logic");
  }

  Node returnNode;

  switch (oldKind)
  {
    // ---- bit-width query ---------------------------------------------------
    case Kind::PBV_SIZE:
    {
      // CONV(|t|) = κ(t)
      returnNode = computeKappa(original[0]);
      break;
    }

    // ---- int-to-pbv injection ----------------------------------------------
    case Kind::INT_TO_PBV:
    {
      // CONV(to-pbv(k, t)) = CONV(t) mod pow2(k)
      // translated_children[0] = k (Int), translated_children[1] = CONV(t)
      Node k = translated_children[0];
      Node t = translated_children[1];
      // Skip the modulo when t is statically known to be in [0, pow2(k)):
      //   * t == 0 or t == 1
      //   * t == k       (k < pow2(k) since the ADM constraint enforces k > 0)
      //   * t == pow2(k') - 1   (i.e. CONV(pbvnot (int_to_pbv k' 0))).
      //     Sound iff k' <= k; we rely on this holding by construction
      //     (in practice the surrounding admissibility constraints enforce
      //     matching widths whenever this pattern is wrapped in int_to_pbv).
      //   * t == (x mod pow2(k))    — already mod'd at the same width
      //   * t == piand(k, _, _)     — piand result is bounded by its width arg
      bool inRange = (t == d_zero) || (t == d_one) || (t == k);
      if (!inRange && t.getKind() == Kind::SUB && t.getNumChildren() == 2
          && t[0].getKind() == Kind::EXP && t[0][0] == d_two
          && t[1] == d_one)
      {
        inRange = true;
      }
      if (!inRange && t.getKind() == Kind::INTS_MODULUS_TOTAL
          && t[1].getKind() == Kind::EXP && t[1][0] == d_two && t[1][1] == k)
      {
        inRange = true;
      }
      if (!inRange && t.getKind() == Kind::PIAND && t[0] == k)
      {
        inRange = true;
      }
      returnNode = inRange ? t : modPow2Sym(t, k);
      break;
    }

    // ---- equality / comparisons --------------------------------------------
    case Kind::EQUAL:
    {
      returnNode = d_nm->mkNode(Kind::EQUAL, translated_children);
      break;
    }
    case Kind::PBV_ULT:
    {
      returnNode = d_nm->mkNode(
          Kind::LT, translated_children[0], translated_children[1]);
      break;
    }
    case Kind::PBV_ULE:
    {
      returnNode = d_nm->mkNode(
          Kind::LEQ, translated_children[0], translated_children[1]);
      break;
    }
    case Kind::PBV_UGT:
    {
      returnNode = d_nm->mkNode(
          Kind::GT, translated_children[0], translated_children[1]);
      break;
    }
    case Kind::PBV_UGE:
    {
      returnNode = d_nm->mkNode(
          Kind::GEQ, translated_children[0], translated_children[1]);
      break;
    }
    case Kind::PBV_SLT:
    {
      // uts(κ(t1), CONV(t1)) < uts(κ(t1), CONV(t2))
      Node k1 = computeKappa(original[0]);
      returnNode = d_nm->mkNode(Kind::LT,
                                utsSym(k1, translated_children[0]),
                                utsSym(k1, translated_children[1]));
      break;
    }
    case Kind::PBV_SLE:
    {
      Node k1 = computeKappa(original[0]);
      returnNode = d_nm->mkNode(Kind::LEQ,
                                utsSym(k1, translated_children[0]),
                                utsSym(k1, translated_children[1]));
      break;
    }
    case Kind::PBV_SGT:
    {
      Node k1 = computeKappa(original[0]);
      returnNode = d_nm->mkNode(Kind::GT,
                                utsSym(k1, translated_children[0]),
                                utsSym(k1, translated_children[1]));
      break;
    }
    case Kind::PBV_SGE:
    {
      Node k1 = computeKappa(original[0]);
      returnNode = d_nm->mkNode(Kind::GEQ,
                                utsSym(k1, translated_children[0]),
                                utsSym(k1, translated_children[1]));
      break;
    }

    // ---- arithmetic operations ---------------------------------------------
    case Kind::PBV_ADD:
    {
      Assert(original.getNumChildren() == 2);
      Node k1 = computeKappa(original[0]);
      returnNode = modPow2Sym(
          d_nm->mkNode(Kind::ADD, translated_children[0], translated_children[1]),
          k1);
      break;
    }
    case Kind::PBV_SUB:
    {
      Node k1 = computeKappa(original[0]);
      returnNode = modPow2Sym(
          d_nm->mkNode(Kind::SUB, translated_children[0], translated_children[1]),
          k1);
      break;
    }
    case Kind::PBV_MULT:
    {
      Assert(original.getNumChildren() == 2);
      Node k1 = computeKappa(original[0]);
      returnNode = modPow2Sym(
          d_nm->mkNode(Kind::MULT,
                       translated_children[0], translated_children[1]),
          k1);
      break;
    }
    case Kind::PBV_NEG:
    {
      // (-^B t) = (pow2(k) - CONV(t)) mod pow2(k)
      Node k = computeKappa(original[0]);
      Node neg = d_nm->mkNode(Kind::SUB, mkPow2Sym(k), translated_children[0]);
      returnNode = modPow2Sym(neg, k);
      break;
    }
    case Kind::PBV_UDIV:
    {
      // ite(CONV(t2) = 0,  pow2(k1)-1,  CONV(t1) div CONV(t2))
      Node k1      = computeKappa(original[0]);
      Node isZero  = d_nm->mkNode(Kind::EQUAL, translated_children[1], d_zero);
      Node allOnes = d_nm->mkNode(Kind::SUB, mkPow2Sym(k1), d_one);
      Node divRes  = d_nm->mkNode(Kind::INTS_DIVISION_TOTAL,
                                  translated_children[0],
                                  translated_children[1]);
      returnNode = d_nm->mkNode(Kind::ITE, isZero, allOnes, divRes);
      break;
    }
    case Kind::PBV_UREM:
    {
      // ite(CONV(t2) = 0,  CONV(t1),  CONV(t1) mod CONV(t2))
      Node isZero  = d_nm->mkNode(Kind::EQUAL, translated_children[1], d_zero);
      Node remRes  = d_nm->mkNode(Kind::INTS_MODULUS_TOTAL,
                                  translated_children[0],
                                  translated_children[1]);
      returnNode = d_nm->mkNode(Kind::ITE,
                                isZero, translated_children[0], remRes);
      break;
    }

    // ---- bitwise operations ------------------------------------------------
    case Kind::PBV_NOT:
    {
      // ~^B t  =  pow2(k) - (CONV(t) + 1)
      Node k = computeKappa(original[0]);
      if (translated_children[0] == d_zero)
      {
        // ~0 = pow2(k) - 1
        returnNode = d_nm->mkNode(Kind::SUB, mkPow2Sym(k), d_one);
      }
      else
      {
        Node xPlusOne =
            d_nm->mkNode(Kind::ADD, translated_children[0], d_one);
        returnNode = d_nm->mkNode(Kind::SUB, mkPow2Sym(k), xPlusOne);
      }
      break;
    }
    case Kind::PBV_AND:
    {
      // t1 & t2  =  piand(κ(t1), CONV(t1), CONV(t2))
      Node k1    = computeKappa(original[0]);
      returnNode = d_nm->mkNode(Kind::PIAND,
                                k1,
                                translated_children[0],
                                translated_children[1]);
      break;
    }
    case Kind::PBV_OR:
    {
      // t1 | t2  =  CONV(t1) + CONV(t2) - piand(κ(t1), CONV(t1), CONV(t2))
      // (No mod needed: result is already in [0, pow2(k1)) by Lemma 9.)
      Node k1       = computeKappa(original[0]);
      Node piandNode = d_nm->mkNode(Kind::PIAND,
                                    k1,
                                    translated_children[0],
                                    translated_children[1]);
      returnNode = d_nm->mkNode(
          Kind::SUB,
          d_nm->mkNode(Kind::ADD,
                       translated_children[0], translated_children[1]),
          piandNode);
      break;
    }
    case Kind::PBV_XOR:
    {
      // t1 ⊕ t2  =  CONV(t1) + CONV(t2) - 2 * piand(κ(t1), CONV(t1), CONV(t2))
      Node k1        = computeKappa(original[0]);
      Node piandNode = d_nm->mkNode(Kind::PIAND,
                                    k1,
                                    translated_children[0],
                                    translated_children[1]);
      Node twice     = d_nm->mkNode(Kind::MULT, d_two, piandNode);
      returnNode = d_nm->mkNode(
          Kind::SUB,
          d_nm->mkNode(Kind::ADD,
                       translated_children[0], translated_children[1]),
          twice);
      break;
    }

    // ---- shift operations --------------------------------------------------
    case Kind::PBV_SHL:
    {
      // t1 << t2  =  (CONV(t1) * pow2(CONV(t2))) mod pow2(κ(t1))
      Node k1      = computeKappa(original[0]);
      Node shifted = d_nm->mkNode(Kind::MULT,
                                  translated_children[0],
                                  mkPow2Sym(translated_children[1]));
      returnNode = modPow2Sym(shifted, k1);
      break;
    }
    case Kind::PBV_LSHR:
    {
      // t1 >>_l t2  =  CONV(t1) div pow2(CONV(t2))
      // (Range constraints guarantee t2 < k, so if t2 >= k the result is 0.)
      returnNode = d_nm->mkNode(Kind::INTS_DIVISION_TOTAL,
                                translated_children[0],
                                mkPow2Sym(translated_children[1]));
      break;
    }
    case Kind::PBV_ASHR:
    {
      // Arithmetic right shift: fill vacated bits with the sign bit.
      //   if CONV(t1) < pow2(k-1):   result = t1 div pow2(t2)          [MSB=0]
      //   if CONV(t1) >= pow2(k-1):  result = pow2(k)-1 - ((pow2(k)-1-t1) div pow2(t2))  [MSB=1]
      Node k        = computeKappa(original[0]);
      Node pow2k    = mkPow2Sym(k);
      Node kMinus1  = d_nm->mkNode(Kind::SUB, k, d_one);
      Node signedMin = mkPow2Sym(kMinus1);
      Node pow2shift = mkPow2Sym(translated_children[1]);

      // Unsigned (MSB=0) branch
      Node unsignedResult = d_nm->mkNode(Kind::INTS_DIVISION_TOTAL,
                                         translated_children[0],
                                         pow2shift);
      // Signed (MSB=1) branch: ~(~t1 >> t2)
      Node allOnes   = d_nm->mkNode(Kind::SUB, pow2k, d_one);
      Node complement = d_nm->mkNode(Kind::SUB, allOnes, translated_children[0]);
      Node shiftedComplement = d_nm->mkNode(Kind::INTS_DIVISION_TOTAL,
                                            complement, pow2shift);
      Node signedResult = d_nm->mkNode(Kind::SUB, allOnes, shiftedComplement);

      Node isSigned = d_nm->mkNode(Kind::GEQ, translated_children[0], signedMin);
      returnNode = d_nm->mkNode(Kind::ITE, isSigned, signedResult, unsignedResult);
      break;
    }

    // ---- structural operations ---------------------------------------------
    case Kind::PBV_CONCAT:
    {
      // t1 ○ t2  =  CONV(t1) * pow2(κ(t2)) + CONV(t2)
      Node k2    = computeKappa(original[1]);
      returnNode = d_nm->mkNode(
          Kind::ADD,
          d_nm->mkNode(Kind::MULT, translated_children[0], mkPow2Sym(k2)),
          translated_children[1]);
      break;
    }
    case Kind::PBV_EXTRACT:
    {
      // t[i:j]  =  (CONV(t) div pow2(j)) mod pow2(i - j + 1)
      // translated_children[0] = CONV(t),  [1] = i,  [2] = j
      Node i      = translated_children[1];
      Node j      = translated_children[2];
      Node width  = d_nm->mkNode(
          Kind::ADD, d_nm->mkNode(Kind::SUB, i, j), d_one);
      Node divRes = d_nm->mkNode(Kind::INTS_DIVISION_TOTAL,
                                 translated_children[0],
                                 mkPow2Sym(j));
      returnNode  = modPow2Sym(divRes, width);
      break;
    }
    case Kind::PBV_ZERO_EXTEND:
    {
      // zero_extend(n, t): integer value unchanged, just wider.
      // translated_children[0] = n,  [1] = CONV(t)
      returnNode = translated_children[1];
      break;
    }
    case Kind::PBV_SIGN_EXTEND:
    {
      // sign_extend(n, t):
      //   if CONV(t) >= pow2(κ(t)-1):  (pow2(n)-1)*pow2(κ(t)) + CONV(t)
      //   else:                         CONV(t)
      // translated_children[0] = n,  [1] = CONV(t)
      Node n        = translated_children[0];
      Node xp       = translated_children[1];
      Node k        = computeKappa(original[1]);
      Node kMinus1  = d_nm->mkNode(Kind::SUB, k, d_one);
      Node signedMin = mkPow2Sym(kMinus1);
      // MSB is 1 iff xp >= pow2(k-1)
      Node msbOne   = d_nm->mkNode(Kind::GEQ, xp, signedMin);
      // Extension = (pow2(n) - 1) * pow2(k) + xp
      Node extension = d_nm->mkNode(
          Kind::ADD,
          d_nm->mkNode(Kind::MULT,
                       d_nm->mkNode(Kind::SUB, mkPow2Sym(n), d_one),
                       mkPow2Sym(k)),
          xp);
      returnNode = d_nm->mkNode(Kind::ITE, msbOne, extension, xp);
      break;
    }

    // ---- ITE over PBV ------------------------------------------------------
    case Kind::ITE:
    {
      if (original.getType().isPbv())
      {
        // ITE(cond, t2, t3) with PBV branches: just rebuild over Int translations
        returnNode = d_nm->mkNode(Kind::ITE,
                                  translated_children[0],
                                  translated_children[1],
                                  translated_children[2]);
      }
      else
      {
        // Non-PBV ITE (e.g., Int or Bool): reconstruct as-is
        TypeNode resultType = original.getType();
        returnNode = reconstructNode(original, resultType, translated_children);
      }
      break;
    }

    // ---- quantifiers -------------------------------------------------------
    // Per the paper (runtype + runrange flow through quantifiers): for each
    // bound PBV variable x of width k_x add the guard
    //   k_x > 0  ∧  0 ≤ x_int  ∧  x_int < pow2(k_x)
    // alongside the existing bound x_int. The guard is the antecedent under
    // FORALL and a conjunct under EXISTS.
    case Kind::FORALL:
    case Kind::EXISTS:
    {
      Node oldVarList = original[0];
      std::vector<Node> newBVars;
      std::vector<Node> guards;
      for (const Node& bvar : oldVarList)
      {
        Assert(d_intblastCache.find(bvar) != d_intblastCache.end());
        Node bvarTranslated = d_intblastCache[bvar].get();
        Assert(!bvarTranslated.isNull());
        newBVars.push_back(bvarTranslated);
        if (bvar.getType().isPbv())
        {
          // Bound kappa was registered by registerBoundKappas pre-pass.
          Assert(d_kappaMap.find(bvar) != d_kappaMap.end());
          Node kappa = d_kappaMap[bvar].get();
          newBVars.push_back(kappa);
          Node g = d_nm->mkNode(Kind::AND,
              {d_nm->mkNode(Kind::GT, kappa, d_zero),
               d_nm->mkNode(Kind::LEQ, d_zero, bvarTranslated),
               d_nm->mkNode(Kind::LT, bvarTranslated, mkPow2Sym(kappa))});
          guards.push_back(g);
        }
      }
      Node body = translated_children[1];
      Node newBody;
      if (guards.empty())
      {
        newBody = body;
      }
      else
      {
        Node guardConj = guards.size() == 1
                             ? guards[0]
                             : d_nm->mkNode(Kind::AND, guards);
        newBody = (oldKind == Kind::FORALL)
                      ? d_nm->mkNode(Kind::IMPLIES, guardConj, body)
                      : d_nm->mkNode(Kind::AND, guardConj, body);
      }
      Node newVarList = d_nm->mkNode(Kind::BOUND_VAR_LIST, newBVars);
      returnNode = d_nm->mkNode(oldKind, newVarList, newBody);
      break;
    }

    // ---- default: non-PBV operators ----------------------------------------
    default:
    {
      // Verify we have not missed any PBV operator
      Assert(theory::kindToTheoryId(oldKind) != THEORY_PBV);

      TypeNode resultType;
      if (original.getType().isBitVector())
      {
        resultType = d_nm->integerType();
      }
      else
      {
        resultType = original.getType();
      }
      returnNode = reconstructNode(original, resultType, translated_children);
      break;
    }
  }

  Trace("pint-blaster-debug") << "translateWithChildren: " << original
                              << " => " << returnNode << std::endl;
  Assert(!returnNode.isNull());
  return returnNode;
}

// ============================================================================
// translateFunctionSymbol
// ============================================================================

Node PIntBlaster::translateFunctionSymbol(Node bvUF,
                                          std::map<Node, Node>& skolems)
{
  SkolemManager* sm = d_nm->getSkolemManager();
  Node intUF = sm->mkSkolemFunction(SkolemId::BV_TO_INT_UF, bvUF);

  std::vector<Node> args;
  std::vector<Node> achildren;
  achildren.push_back(intUF);

  int i = 0;
  TypeNode tn      = bvUF.getType();
  TypeNode bvRange = tn.getRangeType();
  std::vector<TypeNode> bvDomain = tn.getArgTypes();

  for (const TypeNode& d : bvDomain)
  {
    Node fresh_bound_var = NodeManager::mkBoundVar(d);
    args.push_back(fresh_bound_var);
    Node castedArg = args[i];
    if (d.isBitVector() || d.isPbv())
    {
      castedArg = castToType(castedArg, d_nm->integerType());
    }
    achildren.push_back(castedArg);
    i++;
  }

  Node app    = d_nm->mkNode(Kind::APPLY_UF, achildren);
  Node body   = castToType(app, bvRange);
  Node bvlist = d_nm->mkNode(Kind::BOUND_VAR_LIST, args);
  Node result = d_nm->mkNode(Kind::LAMBDA, bvlist, body);

  if (skolems.find(bvUF) == skolems.end())
  {
    skolems[bvUF] = result;
  }
  return intUF;
}

// ============================================================================
// castToType
// ============================================================================

Node PIntBlaster::castToType(Node n, TypeNode tn)
{
  if (n.getType() == tn) return n;

  TypeNode nType = n.getType();

  // Int → BV
  if (nType.isInteger() && tn.isBitVector())
  {
    unsigned bvsize = tn.getBitVectorSize();
    Node intToBVOp  = d_nm->mkConst<IntToBitVector>(IntToBitVector(bvsize));
    return d_nm->mkNode(intToBVOp, n);
  }
  // BV → Int
  if (nType.isBitVector() && tn.isInteger())
  {
    return d_nm->mkNode(Kind::BITVECTOR_UBV_TO_INT, n);
  }
  // PBV → Int or Int → PBV: PBV nodes are handled explicitly in
  // translateWithChildren; this path is a safe no-op fallback.
  if ((nType.isPbv() && tn.isInteger())
      || (nType.isInteger() && tn.isPbv()))
  {
    return n;
  }
  // Should not be reached for other type combinations.
  Assert(false) << "castToType: unsupported cast from " << nType << " to "
                << tn;
  return n;
}

// ============================================================================
// childrenTypesChanged
// ============================================================================

bool PIntBlaster::childrenTypesChanged(Node n)
{
  for (const Node& child : n)
  {
    if (d_intblastCache.find(child) != d_intblastCache.end())
    {
      if (d_intblastCache[child].get().getType() != child.getType())
      {
        return true;
      }
    }
  }
  return false;
}

// ============================================================================
// reduceRedundantMods — post-walker that strips redundant nested mods.
//
// After CONV, expressions like  ((a mod p) + (b mod p)) mod p  are common.
// The inner mods are redundant: arithmetic distributes over mod for +, -, *.
// Mirrors the smt-switch `PostPBVWalker::visit_term` rewrite.
// ============================================================================

Node PIntBlaster::rmModIfRedundant(Node node, Node modValue)
{
  // Recursively strip every  `(_ mod modValue)`  anywhere in the subtree.
  //
  // CAUTION (soundness): this is generally unsound. Only ADD, SUB, MULT
  // and ITE distribute over mod, so stripping inner mods inside other
  // operators (division, comparisons, uninterpreted functions, etc.)
  // changes the value of the expression. Enabled here per user request —
  // assumes the surrounding PBV pipeline only emits inner mods in places
  // where mod-distribution holds. If a regression appears, narrow the set
  // of recursed kinds (see git history for the prior, kind-gated version).
  //
  // Also folds 0 * _ → 0 at any depth.
  if (node.getKind() == Kind::INTS_MODULUS_TOTAL && node[1] == modValue)
  {
    return rmModIfRedundant(node[0], modValue);
  }
  if (node.getNumChildren() == 0)
  {
    return node;
  }
  Kind k = node.getKind();
  std::vector<Node> kids;
  kids.reserve(node.getNumChildren());
  bool changed = false;
  bool sawZero = false;
  for (const Node& c : node)
  {
    Node nc = rmModIfRedundant(c, modValue);
    if (nc != c) changed = true;
    if (k == Kind::MULT && nc == d_zero) sawZero = true;
    kids.push_back(nc);
  }
  if (k == Kind::MULT && sawZero) return d_zero;
  if (!changed) return node;
  // Rebuild while preserving the operator for parameterized kinds.
  NodeBuilder nb(d_nm, k);
  if (node.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    nb << node.getOperator();
  }
  for (const Node& c : kids)
  {
    nb << c;
  }
  return nb.constructNode();
}

Node PIntBlaster::reduceRedundantMods(Node n)
{
  std::unordered_map<Node, Node> cache;
  std::vector<Node> toVisit{n};

  while (!toVisit.empty())
  {
    Node cur = toVisit.back();
    auto it = cache.find(cur);
    if (it == cache.end())
    {
      cache[cur] = Node();
      for (const Node& c : cur)
      {
        toVisit.push_back(c);
      }
      continue;
    }
    if (!it->second.isNull())
    {
      toVisit.pop_back();
      continue;
    }
    toVisit.pop_back();

    Node result;
    Kind k = cur.getKind();

    if (cur.getNumChildren() == 0)
    {
      result = cur;
    }
    else
    {
      // Collect rewritten children
      std::vector<Node> newChildren;
      newChildren.reserve(cur.getNumChildren());
      bool childChanged = false;
      for (const Node& c : cur)
      {
        Node nc = cache[c];
        Assert(!nc.isNull());
        if (nc != c) childChanged = true;
        newChildren.push_back(nc);
      }

      // For every outer  (_ mod modValue),  recurse through the entire body
      // and strip every redundant inner `mod modValue` (any kind, any depth).
      // A 0*_ fold along the way collapses the whole mod to 0.
      bool rewritten = false;
      if (k == Kind::INTS_MODULUS_TOTAL && newChildren.size() == 2)
      {
        Node lhs = newChildren[0];
        Node modValue = newChildren[1];
        Node newLhs = rmModIfRedundant(lhs, modValue);
        if (newLhs != lhs)
        {
          result = (newLhs == d_zero)
                       ? d_zero
                       : d_nm->mkNode(
                           Kind::INTS_MODULUS_TOTAL, newLhs, modValue);
          rewritten = true;
        }
      }

      if (!rewritten)
      {
        if (!childChanged)
        {
          result = cur;
        }
        else
        {
          NodeBuilder nb(d_nm, k);
          if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
          {
            nb << cur.getOperator();
          }
          for (const Node& c : newChildren)
          {
            nb << c;
          }
          result = nb.constructNode();
        }
      }
    }

    Assert(!result.isNull());
    cache[cur] = result;
  }

  return cache[n];
}

// ============================================================================
// detectSelfSquaring — find  (= x (mod (* x x) p))  and emit  x <= 1
// ============================================================================

void PIntBlaster::detectSelfSquaring(Node n, std::vector<TrustNode>& lemmas)
{
  std::unordered_set<Node> visited;
  std::vector<Node> stack{n};
  while (!stack.empty())
  {
    Node cur = stack.back();
    stack.pop_back();
    if (!visited.insert(cur).second) continue;

    if (cur.getKind() == Kind::EQUAL && cur.getNumChildren() == 2)
    {
      // Try both orientations:  (= x M)  and  (= M x).
      for (int side = 0; side < 2; ++side)
      {
        Node x = cur[side];
        Node y = cur[1 - side];
        if (y.getKind() != Kind::INTS_MODULUS_TOTAL
            || y.getNumChildren() != 2)
          continue;
        Node body = y[0];
        if (body.getKind() != Kind::MULT || body.getNumChildren() != 2)
          continue;
        if (body[0] != x || body[1] != x) continue;

        //  (=> (= x (mod (* x x) p))  (<= x 1))
        Node xLeOne = d_nm->mkNode(Kind::LEQ, x, d_one);
        Node lemma = d_nm->mkNode(Kind::IMPLIES, cur, xLeOne);
        if (!d_rangeAssertions.contains(lemma))
        {
          d_rangeAssertions.insert(lemma);
          lemmas.push_back(TrustNode::mkTrustLemma(lemma, this));
          Trace("pint-blaster") << "SELF-SQUARING: " << lemma << std::endl;
        }
        break;  // don't double-emit for both orientations
      }
    }

    for (const Node& c : cur)
    {
      stack.push_back(c);
    }
  }
}

// ============================================================================
// reconstructNode
// ============================================================================

Node PIntBlaster::reconstructNode(Node originalNode,
                                  TypeNode resultType,
                                  const std::vector<Node>& translated_children)
{
  Kind oldKind = originalNode.getKind();
  NodeBuilder builder(nodeManager(), oldKind);
  if (originalNode.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    builder << originalNode.getOperator();
  }
  for (uint32_t i = 0; i < originalNode.getNumChildren(); i++)
  {
    Node originalChild   = originalNode[i];
    Node translatedChild = translated_children[i];
    Node adjustedChild   = castToType(translatedChild, originalChild.getType());
    builder << adjustedChild;
  }
  Node reconstruction = builder.constructNode();
  reconstruction = castToType(reconstruction, resultType);
  return reconstruction;
}

}  // namespace cvc5::internal
