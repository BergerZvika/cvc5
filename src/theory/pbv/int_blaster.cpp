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

#include <functional>
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

  // Early-out for pure-BV input: the pbv-to-int pass runs unconditionally,
  // but on a QF_BV assertion with no PBV term anywhere there is nothing to
  // translate. Without this, the default branch in translateWithChildren
  // would force BV results to Int and emit `ubv_to_int(...)`, which is not
  // a legal QF_BV atom.
  {
    std::unordered_set<Node> seen;
    std::vector<Node> st{n};
    bool hasPbv = false;
    while (!st.empty() && !hasPbv)
    {
      Node m = st.back();
      st.pop_back();
      if (!seen.insert(m).second) continue;
      if (m.getType().isPbv())
      {
        hasPbv = true;
        break;
      }
      for (const Node& c : m) st.push_back(c);
    }
    if (!hasPbv)
    {
      return TrustNode::null();
    }
  }

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
  // Record ADM(n) separately from RANGE(n): --pbv-type-check discharges the
  // admissibility constraint on its own, as the width-only obligation that
  // decides whether the formula is well-sorted at all.
  size_t admStart = lemmas.size();
  addAdmConstraints(n, lemmas);
  for (size_t i = admStart, iend = lemmas.size(); i < iend; ++i)
  {
    d_admConstraints.push_back(lemmas[i].getProven());
  }

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
  // Bound PBV variables ARE valid leaves: by unifying them in the union-find
  // with the free PBV variables they are forced to share a width with (e.g.
  // `pbvadd x s` forces κ_x = κ_s), the bound variable can borrow the class's
  // free kappa skolem instead of needing its own quantified kappa. This
  // avoids the admissibility-constraint capture problem where two free
  // kappas tied to a single bound kappa would be related only inside the
  // quantifier (and so end up as a disjunct in the negated form).
  while (true)
  {
    if (t.isVar() && t.getType().isPbv())
    {
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

        // Reject an explicit width expression `ek` if it mentions PBV_SIZE
        // anywhere (regardless of which class the inner var belongs to).
        // The post-translation output must be pure UFNIA — `(pbvsize ...)`
        // is a PBV-theory call and cannot leak into kappa values, otherwise
        // every translated assertion using that kappa keeps `pbvsize` live.
        // Names kept (`selfRefExplicit`, parameter `rep`) for diff minimality.
        auto selfRefExplicit = [&](Node ek, Node /*rep*/) -> bool {
          std::vector<Node> stack{ek};
          while (!stack.empty())
          {
            Node n = stack.back();
            stack.pop_back();
            if (n.getKind() == Kind::PBV_SIZE) return true;
            for (const Node& kid : n) stack.push_back(kid);
          }
          return false;
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
            if (d_kappaClassExplicit.find(rep) == d_kappaClassExplicit.end()
                && !selfRefExplicit(ek0, rep))
              d_kappaClassExplicit[rep] = ek0;
          }
          if (!src0.isNull() && !eki.isNull())
          {
            Node rep = kappaFind(src0);
            if (d_kappaClassExplicit.find(rep) == d_kappaClassExplicit.end()
                && !selfRefExplicit(eki, rep))
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

    // Explicit-kappa pin: `(= (pbvsize V) ek)` (or symmetric) lets us treat
    // `ek` as the kappa for V's whole equivalence class, instead of
    // allocating a fresh `_k` skolem. We accept any non-PBV_SIZE-bearing
    // expression — typically an integer constant from the BV→PBV lifter.
    if (k == Kind::EQUAL && cur.getNumChildren() == 2
        && cur[0].getType().isInteger())
    {
      auto isPbvSizeOfLeaf = [](Node x) -> Node {
        if (x.getKind() == Kind::PBV_SIZE && x.getNumChildren() == 1
            && x[0].isVar() && x[0].getType().isPbv())
        {
          return x[0];
        }
        return Node::null();
      };
      auto mentionsPbvSize = [](Node ek) -> bool {
        std::vector<Node> st{ek};
        while (!st.empty())
        {
          Node m = st.back();
          st.pop_back();
          if (m.getKind() == Kind::PBV_SIZE) return true;
          for (const Node& kid : m) st.push_back(kid);
        }
        return false;
      };
      Node sizeVar;
      Node ek;
      if (!(sizeVar = isPbvSizeOfLeaf(cur[0])).isNull())
      {
        ek = cur[1];
      }
      else if (!(sizeVar = isPbvSizeOfLeaf(cur[1])).isNull())
      {
        ek = cur[0];
      }
      if (!sizeVar.isNull() && !mentionsPbvSize(ek))
      {
        Node rep = kappaFind(sizeVar);
        if (d_kappaClassExplicit.find(rep) == d_kappaClassExplicit.end())
        {
          d_kappaClassExplicit[rep] = ek;
        }
      }
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

  // Bit-vector-typed terms have a fixed, concrete width (e.g. a QF_UFBV
  // function returning `(_ BitVec 10)` whose result is then fed into a PBV
  // operator such as extract). Their κ is simply that width as an integer
  // constant — there is no symbolic kappa to compute. Handling them here
  // keeps mixed BV/PBV terms (produced by lifting BV applications whose
  // operator stays bit-vector-typed) from falling through to the
  // Unimplemented default below.
  if (t.getType().isBitVector())
  {
    Node w = d_nm->mkConstInt(Rational(t.getType().getBitVectorSize()));
    d_kappaMap[t] = w;
    return w;
  }

  Node result;
  Kind k = t.getKind();

  switch (k)
  {
    // to-pbv(width, val): κ = the width argument (first child).
    // If the width argument is itself `(pbvsize V)` (very common in PBV
    // benchmarks), normalize it to computeKappa(V) so admissibility
    // constraints emitted with this kappa equal the same skolem
    // computeKappa hands back elsewhere — without this, the constraint
    // becomes `(= _k (pbvsize s))` which is opaque to the rewriter and
    // ends up as a defeasible disjunct in the negated form.
    case Kind::INT_TO_PBV:
    {
      Node k = t[0];
      if (k.getKind() == Kind::PBV_SIZE && k.getNumChildren() == 1)
      {
        k = computeKappa(k[0]);
      }
      result = k;
      break;
    }
    // t[i:j]: κ = i - j + 1.
    case Kind::PBV_EXTRACT:
    {
      Node i = normalizeWidthExpr(t[1]);
      Node j = normalizeWidthExpr(t[2]);
      result = d_nm->mkNode(
          Kind::ADD, d_nm->mkNode(Kind::SUB, i, j), d_one);
      break;
    }
    // zero_extend(n, t) or sign_extend(n, t): κ = κ(t) + n
    case Kind::PBV_ZERO_EXTEND:
    case Kind::PBV_SIGN_EXTEND:
    {
      result = d_nm->mkNode(
          Kind::ADD, computeKappa(t[1]), normalizeWidthExpr(t[0]));
      break;
    }
    // t[i:j]: κ = (i - j + 1), but indices may be `(pbvsize V)` expressions
    // that the integer solver treats as uninterpreted unless normalized.
    // t1 ○ … ○ tn: κ = κ(t1) + … + κ(tn). PBV_CONCAT is n-ary, and
    // computeKappa runs over the raw (un-binarized) term in the RANGE/ADM
    // walks, so we must sum *every* operand — summing only the first two
    // would under-count the width of a 3+-way concat and make the
    // equal-width admissibility constraint `(= κ_expected κ_concat)` false.
    case Kind::PBV_CONCAT:
    {
      std::vector<Node> kappas;
      for (const Node& c : t)
      {
        kappas.push_back(computeKappa(c));
      }
      result = kappas.size() == 1 ? kappas[0]
                                  : d_nm->mkNode(Kind::ADD, kappas);
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

Node PIntBlaster::normalizeWidthExpr(Node n)
{
  if (n.getKind() == Kind::PBV_SIZE && n.getNumChildren() == 1)
  {
    return computeKappa(n[0]);
  }
  if (n.getNumChildren() == 0)
  {
    return n;
  }
  std::vector<Node> kids;
  bool changed = false;
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    kids.push_back(n.getOperator());
  }
  for (const Node& c : n)
  {
    Node nc = normalizeWidthExpr(c);
    if (nc != c) changed = true;
    kids.push_back(nc);
  }
  return changed ? d_nm->mkNode(n.getKind(), kids) : n;
}

// ============================================================================
// mkPow2Sym / modPow2Sym / utsSym
// ============================================================================

Node PIntBlaster::mkPow2Sym(Node k)
{
  // When the exponent is a concrete non-negative integer constant (the common
  // case once a width comes from a fixed `(_ BitVec w)` sort, as in QF_BV /
  // QF_UFBV), fold `2^k` to the integer constant directly instead of leaving
  // a symbolic `(** 2 w)` / `(int.pow2 w)` term for the rewriter to clean up.
  if (k.isConst() && k.getType().isInteger())
  {
    Rational r = k.getConst<Rational>();
    if (r.sgn() >= 0 && r.isIntegral())
    {
      Integer e = r.getNumerator();
      if (e.fitsUnsignedInt())
      {
        return d_nm->mkConstInt(Rational(Integer(2).pow(e.getUnsignedInt())));
      }
    }
  }
  // Default: (** 2 k). With --pbv-to-int-use-pow2: the internal POW2 operator.
  if (options().smt.pbvToIntUsePow2)
  {
    return d_nm->mkNode(Kind::POW2, k);
  }
  return d_nm->mkNode(Kind::EXP, d_two, k);
}

Kind PIntBlaster::modKind() const
{
  return options().smt.pbvToIntPartialMod ? Kind::INTS_MODULUS
                                          : Kind::INTS_MODULUS_TOTAL;
}

Node PIntBlaster::mkMod(Node n, Node d) { return d_nm->mkNode(modKind(), n, d); }

Node PIntBlaster::modPow2Sym(Node n, Node k)
{
  return mkMod(n, mkPow2Sym(k));
}

Node PIntBlaster::utsSym(Node k, Node x)
{
  // uts(k, z) = 2 * (z mod pow2(k-1)) - z
  // Default (sat25 form): use pow2(k-1) directly, matching the SAT'25 paper.
  // --pbv-uts-with-k switches to the full-k form pow2(k) div 2, avoiding a
  // (- k 1) argument to pow2 (relevant for the POW2 operator path, which is
  // undefined on negative exponents).
  Node halfPow2;
  if (options().smt.pbvUtsWithK)
  {
    halfPow2 = d_nm->mkNode(Kind::INTS_DIVISION_TOTAL, mkPow2Sym(k), d_two);
  }
  else
  {
    halfPow2 = mkPow2Sym(d_nm->mkNode(Kind::SUB, k, d_one));
  }
  Node modPart = d_nm->mkNode(modKind(), x, halfPow2);
  Node twice   = d_nm->mkNode(Kind::MULT, d_two, modPart);
  return d_nm->mkNode(Kind::SUB, twice, x);
}

Node PIntBlaster::bvlshrSym(Node x, Node y, Node k)
{
  Node pow2y = mkPow2Sym(y);
  Node pow2k = mkPow2Sym(k);
  Node intTerm = d_nm->mkNode(Kind::INTS_DIVISION_TOTAL, x, pow2y);
  Node innerCond = d_nm->mkNode(Kind::EQUAL, pow2y, d_zero);
  Node innerThen = d_nm->mkNode(Kind::SUB, pow2k, d_one);
  Node inner = d_nm->mkNode(Kind::ITE, innerCond, innerThen, intTerm);
  Node outerCond = d_nm->mkNode(Kind::EQUAL, pow2k, d_zero);
  Node outerElse = d_nm->mkNode(modKind(), inner, pow2k);
  return d_nm->mkNode(Kind::ITE, outerCond, inner, outerElse);
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

std::unordered_set<Node> PIntBlaster::getWidthSymbols() const
{
  std::unordered_set<Node> res;
  for (const auto& kv : d_kappaClassSkolem)
  {
    if (!kv.second.isNull() && !kv.second.isConst())
    {
      res.insert(kv.second);
    }
  }
  return res;
}

void PIntBlaster::addAdmConstraints(Node e,
                                    std::vector<TrustNode>& lemmas)
{
  // Walk recursively so quantifier scope can be tracked. Constraints whose
  // free variables include any of the bound kappas in the surrounding
  // quantifier(s) must be routed to that quantifier's guard rather than
  // the top-level lemma list — otherwise those bound variables escape
  // their scope and the printer/preprocessor capture them via a free
  // skolem of the same name.
  std::vector<Node> quantStack;
  std::unordered_set<Node> visited;

  // For each quantifier on the stack, gather its TRULY bound integer
  // kappa variables (BOUND_VARIABLE nodes registered by registerBoundKappas).
  // When the union-find lets a bound PBV variable reuse a free class
  // kappa, d_kappaMap[bvar] holds that free skolem — those skolems are
  // not in scope of the quantifier and must not be treated as bound here.
  auto getBoundKappasOf = [&](Node q) -> std::unordered_set<Node> {
    std::unordered_set<Node> result;
    if (q.getNumChildren() < 1) return result;
    for (const Node& bvar : q[0])
    {
      if (bvar.getType().isPbv())
      {
        auto it = d_kappaMap.find(bvar);
        if (it != d_kappaMap.end())
        {
          Node kappa = (*it).second;
          if (kappa.getKind() == Kind::BOUND_VARIABLE)
          {
            result.insert(kappa);
          }
        }
      }
    }
    return result;
  };

  // True iff `n` syntactically contains any node from `targets`.
  auto containsAny = [](Node n,
                        const std::unordered_set<Node>& targets) -> bool {
    if (targets.empty()) return false;
    std::unordered_set<Node> seen;
    std::vector<Node> stack{n};
    while (!stack.empty())
    {
      Node x = stack.back();
      stack.pop_back();
      if (!seen.insert(x).second) continue;
      if (targets.count(x)) return true;
      for (const Node& c : x) stack.push_back(c);
    }
    return false;
  };

  // Helper to add a lemma once. Rewrite first so admissibility constraints
  // that are now trivially true after kappa-equivalence-class allocation
  // (e.g. (= κ κ) for two PBV operands that share a class) get dropped
  // instead of being emitted as `(assert true)`.
  auto addOnce = [&](Node constr) {
    Node simplified = rewrite(constr);
    if (simplified.isConst() && simplified.getConst<bool>()) return;

    // If `simplified` mentions any bound kappa from a surrounding quantifier,
    // route it to the innermost such quantifier's guard.
    for (auto rit = quantStack.rbegin(); rit != quantStack.rend(); ++rit)
    {
      auto bk = getBoundKappasOf(*rit);
      if (containsAny(simplified, bk))
      {
        d_quantAdmConstraints[*rit].push_back(simplified);
        Trace("pint-blaster")
            << "ADM (in-quant): " << simplified << std::endl;

        // Recover the value of the bound kappa from a solved-form
        // equality `(= bound_kappa free_expr)` (or its mirror) and
        // assert `free_expr > 0` at top level. Without this, kappa
        // positivity stays inside the quantifier and gets pulled into
        // the negated form as a free disjunct (`κ ≤ 0`) that the solver
        // can satisfy by picking widths where no valid bound x exists,
        // producing a vacuous SAT.
        return;
      }
    }

    if (!d_rangeAssertions.contains(simplified))
    {
      d_rangeAssertions.insert(simplified);
      lemmas.push_back(TrustNode::mkTrustLemma(simplified, this));
      Trace("pint-blaster") << "ADM: " << simplified << std::endl;
    }
  };

  std::function<void(Node)> walk = [&](Node current) {
    if (!visited.insert(current).second) return;
    Kind k = current.getKind();

    // Paper Fig. fig:type, function runtype:
    //   x  -> runbw(x) > 0           (bit-widths are strictly positive)
    //
    // Bound PBV variables also get this positivity, because their kappa
    // is now a top-level free term (a class skolem, see
    // registerBoundKappas). The only kappas we cannot assert about at
    // top level are integer BOUND_VARIABLE nodes — which after the
    // registerBoundKappas change shouldn't appear, but the guard is
    // kept defensively.
    if (current.isVar() && current.getType().isPbv())
    {
      Node kappa = computeKappa(current);
      if (kappa.getKind() != Kind::BOUND_VARIABLE)
      {
        addOnce(d_nm->mkNode(Kind::GT, kappa, d_zero));
      }
    }

    //   int_to_pbv(k, t)  ->  k > 0
    // Route through computeKappa so that `k = (pbvsize V)` is resolved to
    // the integer kappa skolem rather than left as a PBV-theory call.
    if (k == Kind::INT_TO_PBV)
    {
      addOnce(d_nm->mkNode(Kind::GT, computeKappa(current), d_zero));
    }

    //   extract(t, i, j)  ->  0 <= j <= i < runbw(t)
    if (k == Kind::PBV_EXTRACT)
    {
      Node t = current[0];
      Node i = normalizeWidthExpr(current[1]);
      Node j = normalizeWidthExpr(current[2]);
      Node kappaT = computeKappa(t);
      addOnce(d_nm->mkNode(Kind::LEQ, d_zero, j));
      addOnce(d_nm->mkNode(Kind::LEQ, j, i));
      addOnce(d_nm->mkNode(Kind::LT, i, kappaT));
    }

    //   zero_extend(n, t) / sign_extend(n, t)  ->  n >= 0
    if (k == Kind::PBV_ZERO_EXTEND || k == Kind::PBV_SIGN_EXTEND)
    {
      addOnce(d_nm->mkNode(Kind::LEQ, d_zero, normalizeWidthExpr(current[0])));
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

    if (k == Kind::FORALL || k == Kind::EXISTS)
    {
      quantStack.push_back(current);
      // Walk only the body — the bound-var list itself contains
      // BOUND_VARIABLEs that don't need admissibility reasoning here.
      walk(current[1]);
      quantStack.pop_back();
    }
    else
    {
      for (const Node& child : current)
      {
        walk(child);
      }
    }
  };

  walk(e);
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
          // The width of a bound PBV variable is always a TOP-LEVEL
          // integer term, never a quantified BoundVar. We have two
          // sub-cases:
          //
          //  (a) Union-find has unified bvar with a free PBV term (this
          //      catches the common `forall x. x op y` shape via the
          //      equal-width binary-op rule in buildKappaUnionFind):
          //      reuse that class's existing free kappa skolem so the
          //      widths are syntactically identified.
          //
          //  (b) No admissibility tie was discovered (e.g. bvar appears
          //      only inside structural ops like pconcat): allocate a
          //      fresh top-level kappa skolem for bvar's own class.
          //      Any admissibility equation involving κ_bvar is then
          //      enforced as a top-level constraint between free terms.
          //
          // Either way, the kappa is non-bound, the standard kappa>0
          // positivity is emitted by addAdmConstraints, and no escape
          // through the negated existential is possible.
          Node kappa = getOrCreateKappa(bvar);
          Trace("pint-blaster")
              << "BOUND-KAPPA-FREE: " << bvar << " => " << kappa << std::endl;
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
      // Helpers that recognize `pow2(e)` in either of the two encodings the
      // PBV→Int blaster may produce: EXP form `(** 2 e)` (default) or
      // POW2 form `(int.pow2 e)` (--pbv-to-int-use-pow2).
      auto isPow2Of = [&](TNode n, TNode e) {
        return (n.getKind() == Kind::EXP && n[0] == d_two && n[1] == e)
               || (n.getKind() == Kind::POW2 && n[0] == e);
      };
      auto isPow2Any = [&](TNode n) {
        return (n.getKind() == Kind::EXP && n[0] == d_two)
               || n.getKind() == Kind::POW2;
      };
      bool inRange = (t == d_zero) || (t == d_one) || (t == k);
      if (!inRange && t.getKind() == Kind::SUB && t.getNumChildren() == 2
          && isPow2Any(t[0]) && t[1] == d_one)
      {
        inRange = true;
      }
      if (!inRange
          && (t.getKind() == Kind::INTS_MODULUS_TOTAL
              || t.getKind() == Kind::INTS_MODULUS)
          && isPow2Of(t[1], k))
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
      Node remRes  = d_nm->mkNode(modKind(), translated_children[0], translated_children[1]);
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
      Node k1 = computeKappa(original[0]);
      // Match smt-switch's minimum_sign peephole:
      //   bvshl( (_ bv1 k), bvsub( (_ bvk k), (_ bv1 k) ) ) = (_ bv1 k) << (k-1)
      // PBV constants in cvc5 take the form INT_TO_PBV(width, value), so the
      // pattern is INT_TO_PBV(k, 1) for `(_ bv1 k)` and INT_TO_PBV(k, k) for
      // `(_ bvk k)` (value equals width).
      bool isOne0 = original[0].getKind() == Kind::INT_TO_PBV
                    && original[0][1] == d_one;
      bool subPat = original[1].getKind() == Kind::PBV_SUB
                    && original[1][0].getKind() == Kind::INT_TO_PBV
                    && original[1][0][0] == original[1][0][1]
                    && original[1][1].getKind() == Kind::INT_TO_PBV
                    && original[1][1][1] == d_one;
      if (isOne0 && subPat)
      {
        Node kMinus1 = d_nm->mkNode(Kind::SUB, k1, d_one);
        returnNode = mkPow2Sym(kMinus1);
        break;
      }
      // t1 << t2  =  (CONV(t1) * pow2(CONV(t2))) mod pow2(κ(t1))
      Node shifted = d_nm->mkNode(Kind::MULT,
                                  translated_children[0],
                                  mkPow2Sym(translated_children[1]));
      returnNode = modPow2Sym(shifted, k1);
      break;
    }
    case Kind::PBV_LSHR:
    {
      Node k1 = computeKappa(original[0]);
      returnNode =
          bvlshrSym(translated_children[0], translated_children[1], k1);
      break;
    }
    case Kind::PBV_ASHR:
    {
      // Match smt-switch PrePBVWalker rewrite:
      //   ite( (extract s m-1 m-1) == 0,
      //        (bvlshr s t),
      //        (bvnot (bvlshr (bvnot s) t)) )
      // where m = κ(s). bvlshr uses the wrapped integer form (bvlshrSym),
      // matching the abstract walker's default lshr translation.
      Node k       = computeKappa(original[0]);
      Node kMinus1 = d_nm->mkNode(Kind::SUB, k, d_one);
      Node s       = translated_children[0];
      Node t       = translated_children[1];
      Node allOnes = d_nm->mkNode(Kind::SUB, mkPow2Sym(k), d_one);

      // (extract s m-1 m-1) = (s div pow2(m-1)) mod 2
      Node msb = d_nm->mkNode(modKind(), 
          d_nm->mkNode(Kind::INTS_DIVISION_TOTAL, s, mkPow2Sym(kMinus1)),
          d_two);
      Node msbZero = d_nm->mkNode(Kind::EQUAL, msb, d_zero);

      // (bvlshr s t) using the wrapped form
      Node lshrS = bvlshrSym(s, t, k);

      // (bvnot (bvlshr (bvnot s) t))
      //   bvnot(s) = pow2(m) - (s + 1) = allOnes - s
      Node notS    = d_nm->mkNode(Kind::SUB, allOnes, s);
      Node lshrNot = bvlshrSym(notS, t, k);
      // bvnot(lshrNot) = allOnes - lshrNot
      Node notLshrNot = d_nm->mkNode(Kind::SUB, allOnes, lshrNot);

      returnNode = d_nm->mkNode(Kind::ITE, msbZero, lshrS, notLshrNot);
      break;
    }

    // case Kind::PBV_ASHR:
    // {
    //   // Arithmetic right shift: fill vacated bits with the sign bit.
    //   //   if CONV(t1) < pow2(k-1):   result = t1 div pow2(t2)          [MSB=0]
    //   //   if CONV(t1) >= pow2(k-1):  result = pow2(k)-1 - ((pow2(k)-1-t1) div pow2(t2))  [MSB=1]
    //   Node k        = computeKappa(original[0]);
    //   Node pow2k    = mkPow2Sym(k);
    //   Node kMinus1  = d_nm->mkNode(Kind::SUB, k, d_one);
    //   Node signedMin = mkPow2Sym(kMinus1);
    //   Node pow2shift = mkPow2Sym(translated_children[1]);

    //   // Unsigned (MSB=0) branch
    //   Node unsignedResult = d_nm->mkNode(Kind::INTS_DIVISION_TOTAL,
    //                                      translated_children[0],
    //                                      pow2shift);
    //   // Signed (MSB=1) branch: ~(~t1 >> t2)
    //   Node allOnes   = d_nm->mkNode(Kind::SUB, pow2k, d_one);
    //   Node complement = d_nm->mkNode(Kind::SUB, allOnes, translated_children[0]);
    //   Node shiftedComplement = d_nm->mkNode(Kind::INTS_DIVISION_TOTAL,
    //                                         complement, pow2shift);
    //   Node signedResult = d_nm->mkNode(Kind::SUB, allOnes, shiftedComplement);
    //   Node isSigned = d_nm->mkNode(Kind::GEQ, translated_children[0], signedMin);
    //   returnNode = d_nm->mkNode(Kind::ITE, isSigned, signedResult, unsignedResult);
    //   break;
    // }

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
      // Match smt-switch AbstractPBVWalker::extract(x, i, j):
      //   i == j:             (x div pow2(j)) mod 2          (1-bit extract)
      //   j == 0 && i == 0:   x mod 2
      //   j == 0:             x mod pow2(i + 1)
      //   else:               (x div pow2(j)) mod pow2(i - j + 1)
      Node x = translated_children[0];
      Node i = translated_children[1];
      Node j = translated_children[2];
      if (i == j)
      {
        // 1-bit extract — avoid the symbolic pow2(1) by going direct to `mod 2`.
        Node div = (j == d_zero)
                       ? x
                       : d_nm->mkNode(Kind::INTS_DIVISION_TOTAL, x, mkPow2Sym(j));
        returnNode = d_nm->mkNode(modKind(), div, d_two);
      }
      else if (j == d_zero && i == d_zero)
      {
        returnNode = d_nm->mkNode(modKind(), x, d_two);
      }
      else if (j == d_zero)
      {
        Node iPlusOne = d_nm->mkNode(Kind::ADD, i, d_one);
        returnNode = modPow2Sym(x, iPlusOne);
      }
      else
      {
        Node width = d_nm->mkNode(
            Kind::ADD, d_nm->mkNode(Kind::SUB, i, j), d_one);
        Node divRes = d_nm->mkNode(Kind::INTS_DIVISION_TOTAL, x, mkPow2Sym(j));
        returnNode = modPow2Sym(divRes, width);
      }
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
      // Match smt-switch PrePBVWalker rewrite:
      //   ite( (extract x w-1 w-1) == 1,
      //        concat(max_int_n, x),    // (pow2(n)-1)*pow2(w) + x
      //        concat(0_n, x) )         // = x
      // After the abstract walker translates:
      //   (extract x w-1 w-1) = (x div pow2(w-1)) mod 2
      // translated_children[0] = n (extension width), [1] = CONV(t)
      Node n       = translated_children[0];
      Node xp      = translated_children[1];
      Node k       = computeKappa(original[1]);
      Node kMinus1 = d_nm->mkNode(Kind::SUB, k, d_one);
      Node msb = d_nm->mkNode(modKind(), 
          d_nm->mkNode(Kind::INTS_DIVISION_TOTAL, xp, mkPow2Sym(kMinus1)),
          d_two);
      Node msbOne = d_nm->mkNode(Kind::EQUAL, msb, d_one);
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
      // Match smt-switch exactly: for each bound PBV variable x of width k,
      // add only the per-var guard  0 <= x_int  /\  x_int < pow2(k).
      // No k>0 conjunct, no extra binder for kappa, no admissibility folding.
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
          Assert(d_kappaMap.find(bvar) != d_kappaMap.end());
          Node kappa = d_kappaMap[bvar].get();
          Node g = d_nm->mkNode(Kind::AND,
              {d_nm->mkNode(Kind::LEQ, d_zero, bvarTranslated),
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

    // ---- uninterpreted function application --------------------------------
    case Kind::APPLY_UF:
    {
      // translated_children[0] is the translated function symbol (an Int→Int
      // skolem produced by translateFunctionSymbol); the rest are the
      // translated Int arguments. Rebuild the application over Ints.
      returnNode = d_nm->mkNode(Kind::APPLY_UF, translated_children);

      // The original application had a fixed width (BV) or symbolic width
      // (PBV) range sort, so its translated Int value is bounded by the
      // corresponding pow2. Emit `0 <= app < pow2(width)` unless the
      // application mentions a bound variable (those range constraints are
      // attached under the enclosing quantifier instead).
      if (!expr::hasBoundVar(original))
      {
        TypeNode rt = original.getType();
        Node width;
        if (rt.isBitVector())
        {
          width = d_nm->mkConstInt(Rational(rt.getBitVectorSize()));
        }
        else if (rt.isPbv())
        {
          width = computeKappa(original);
        }
        if (!width.isNull())
        {
          Node range = d_nm->mkNode(
              Kind::AND,
              d_nm->mkNode(Kind::LEQ, d_zero, returnNode),
              d_nm->mkNode(Kind::LT, returnNode, mkPow2Sym(width)));
          Node simplified = rewrite(range);
          if (!(simplified.isConst() && simplified.getConst<bool>())
              && !d_rangeAssertions.contains(simplified))
          {
            d_rangeAssertions.insert(simplified);
            lemmas.push_back(TrustNode::mkTrustLemma(simplified, this));
            Trace("pint-blaster") << "RANGE(uf): " << simplified << std::endl;
          }
        }
      }
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
  // Recursively strip every  `(_ mod modValue)`  inside contexts where mod
  // distributes — i.e. when the surrounding expression is in [-p, p) - safe
  // operators ADD, SUB, MULT, NEG, or ITE branches.  Mod does NOT distribute
  // through EXP's exponent (2^(x mod p) ≠ 2^x mod p), nor through division,
  // PIAND, comparisons, EQUAL, or arbitrary UFs, so we must not descend into
  // those operands.
  //
  // Also folds 0 * _ → 0 at any depth.
  if ((node.getKind() == Kind::INTS_MODULUS_TOTAL
       || node.getKind() == Kind::INTS_MODULUS)
      && node[1] == modValue)
  {
    return rmModIfRedundant(node[0], modValue);
  }
  if (node.getNumChildren() == 0)
  {
    return node;
  }
  Kind k = node.getKind();
  bool distributes = (k == Kind::ADD || k == Kind::SUB || k == Kind::MULT
                      || k == Kind::NEG || k == Kind::ITE);
  if (!distributes)
  {
    return node;
  }
  std::vector<Node> kids;
  kids.reserve(node.getNumChildren());
  bool changed = false;
  bool sawZero = false;
  for (uint32_t i = 0; i < node.getNumChildren(); ++i)
  {
    const Node& c = node[i];
    // ITE: only recurse into the branches (1, 2).  The condition is Boolean
    // and stripping integer mods inside it would change comparison results.
    bool recurse = !(k == Kind::ITE && i == 0);
    Node nc = recurse ? rmModIfRedundant(c, modValue) : c;
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
      if ((k == Kind::INTS_MODULUS_TOTAL || k == Kind::INTS_MODULUS)
          && newChildren.size() == 2)
      {
        Node lhs = newChildren[0];
        Node modValue = newChildren[1];
        Node newLhs = rmModIfRedundant(lhs, modValue);
        if (newLhs != lhs)
        {
          // preserve the original modulus kind (total vs partial)
          result = (newLhs == d_zero) ? d_zero
                                      : d_nm->mkNode(k, newLhs, modValue);
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
        if ((y.getKind() != Kind::INTS_MODULUS_TOTAL
             && y.getKind() != Kind::INTS_MODULUS)
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
