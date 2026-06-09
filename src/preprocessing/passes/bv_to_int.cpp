/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The BVToInt preprocessing pass.
 *
 * Converts bit-vector operations into integer operations.
 *
 */

#include "preprocessing/passes/bv_to_int.h"

#include <cmath>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/node_traversal.h"
#include "expr/skolem_manager.h"
#include "options/smt_options.h"
#include "options/uf_options.h"
#include "theory/bv/theory_bv_rewrite_rules_operator_elimination.h"
#include "theory/bv/theory_bv_rewriter.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"
#include "util/pbv.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace std;
using namespace cvc5::internal::theory;
using namespace cvc5::internal::theory::bv;

BVToInt::BVToInt(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bv-to-int"),
      d_intBlaster(preprocContext->getEnv(),
                   options().smt.solveBVAsInt,
                   options().smt.BVAndIntegerGranularity)
{
  if (options().smt.solveBVAsInt == options::SolveBVAsIntMode::PBV)
  {
    d_pIntBlaster.reset(new PIntBlaster(preprocContext->getEnv()));
  }
}

PreprocessingPassResult BVToInt::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  // vector of boolean nodes for additional constraints
  // this will always contain range constraints
  // and for options::SolveBVAsIntMode::BITWISE, it will
  // also include bitwise assertion constraints
  std::vector<TrustNode> additionalConstraints;
  std::map<Node, Node> skolems;

  // PBV mode: lift each BV assertion to PBV first, then run PIntBlaster.
  if (options().smt.solveBVAsInt == options::SolveBVAsIntMode::PBV)
  {
    NodeManager* nm = nodeManager();
    // Phase 1: lift every assertion. This also populates d_bvVarPbv with the
    // BV-var → PBV-var mapping used by the model-recovery step below.
    std::vector<Node> lifted(assertionsToPreprocess->size());
    bool allLifted = true;
    for (uint64_t i = 0; i < assertionsToPreprocess->size(); ++i)
    {
      assertionsToPreprocess->ensureRewritten(i);
      lifted[i] = liftBvToPbv((*assertionsToPreprocess)[i]);
      if (lifted[i].isNull()) allLifted = false;
    }
    // If any assertion contains a BV operator we cannot lift to PBV (e.g.
    // bvcomp, the overflow predicates), abandon the PBV translation entirely
    // and leave every assertion as native bit-vectors. Translating only the
    // liftable assertions would be unsound: a variable shared between a lifted
    // assertion and an un-lifted one would be replaced by its Int encoding in
    // one place but left as a bit-vector in the other, dropping the constraint
    // that ties them together. The native BV solver handles the whole problem
    // instead. (d_bvVarPbv may have been partially populated by the failed
    // lifts above; that is harmless since nothing below runs.)
    if (!allLifted)
    {
      Trace("bv-to-int-debug")
          << "pbv mode: unsupported BV op, falling back to native BV"
          << std::endl;
      return PreprocessingPassResult::NO_CONFLICT;
    }
    // Phase 1b: append `(= (pbvsize pbv_x) k)` pinning assertions for every
    // lifted BV variable BEFORE we pre-scan, so the PIntBlaster sees them
    // when building the kappa union-find.
    size_t firstPin = assertionsToPreprocess->size();
    for (const auto& [bvVar, pbvVar] : d_bvVarPbv)
    {
      uint32_t k = bvVar.getType().getBitVectorSize();
      Node size = nm->mkNode(Kind::PBV_SIZE, pbvVar);
      Node pin = nm->mkNode(Kind::EQUAL, size, nm->mkConstInt(Rational(k)));
      assertionsToPreprocess->push_back(pin);
    }
    // Phase 1c: pre-scan every lifted assertion (and the pin assertions)
    // so the kappa union-find has global visibility.
    for (uint64_t i = 0; i < assertionsToPreprocess->size(); ++i)
    {
      if (i < lifted.size() && !lifted[i].isNull())
      {
        d_pIntBlaster->scanAssertion(lifted[i]);
      }
      else if (i >= firstPin)
      {
        d_pIntBlaster->scanAssertion((*assertionsToPreprocess)[i]);
      }
    }
    // Phase 2: translate each lifted assertion.
    for (uint64_t i = 0; i < lifted.size(); ++i)
    {
      if (lifted[i].isNull())
      {
        continue;  // contained an unsupported kind — leave assertion alone
      }
      Node bvNode = (*assertionsToPreprocess)[i];
      TrustNode tr = d_pIntBlaster->trustedIntBlast(
          lifted[i], additionalConstraints, skolems);
      if (tr.isNull()) continue;
      Trace("bv-to-int-debug") << "bv  node: " << bvNode << std::endl;
      Trace("bv-to-int-debug") << "pbv node: " << lifted[i] << std::endl;
      Trace("bv-to-int-debug")
          << "int node: " << tr.getProven()[1] << std::endl;
      assertionsToPreprocess->replaceTrusted(i, tr);
      assertionsToPreprocess->ensureRewritten(i);
    }
    // Phase 3: translate the pinning assertions through PIntBlaster too
    // (they're trivial `(= k <const>)` Int equalities after translation).
    for (uint64_t i = firstPin; i < assertionsToPreprocess->size(); ++i)
    {
      TrustNode tr = d_pIntBlaster->trustedIntBlast(
          (*assertionsToPreprocess)[i], additionalConstraints, skolems);
      if (tr.isNull()) continue;
      assertionsToPreprocess->replaceTrusted(i, tr);
      assertionsToPreprocess->ensureRewritten(i);
    }
    // Phase 4: model recovery. PBV var pbv_x ↦ χ(pbv_x) at the Int level;
    // the BV var x is reconstructed as `((_ nat2bv k) χ(pbv_x))`.
    std::map<Node, Node> bvModelDefs;
    for (const auto& [bvVar, pbvVar] : d_bvVarPbv)
    {
      Node chi = d_pIntBlaster->lookupChi(pbvVar);
      if (chi.isNull()) continue;
      uint32_t k = bvVar.getType().getBitVectorSize();
      Node nat2bvOp = nm->mkConst<IntToBitVector>(IntToBitVector(k));
      bvModelDefs[bvVar] = nm->mkNode(nat2bvOp, chi);
    }
    addFinalizeAssertions(assertionsToPreprocess, additionalConstraints);
    addSkolemDefinitions(skolems);
    addSkolemDefinitions(bvModelDefs);
    return PreprocessingPassResult::NO_CONFLICT;
  }

  for (uint64_t i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    // ensure bv rewritten
    assertionsToPreprocess->ensureRewritten(i);
    Node bvNode = (*assertionsToPreprocess)[i];
    TrustNode tr =
        d_intBlaster.trustedIntBlast(bvNode, additionalConstraints, skolems);
    if (tr.isNull())
    {
      // int blaster did not apply
      continue;
    }
    Trace("bv-to-int-debug") << "bv node: " << bvNode << std::endl;
    Trace("bv-to-int-debug") << "int node: " << tr.getProven()[1] << std::endl;
    assertionsToPreprocess->replaceTrusted(i, tr);
    // ensure integer rewritten
    assertionsToPreprocess->ensureRewritten(i);
  }
  addFinalizeAssertions(assertionsToPreprocess, additionalConstraints);
  addSkolemDefinitions(skolems);
  return PreprocessingPassResult::NO_CONFLICT;
}

Node BVToInt::liftBvToPbv(Node n)
{
  auto cached = d_liftCache.find(n);
  if (cached != d_liftCache.end()) return cached->second;
  NodeManager* nm = nodeManager();
  Kind k = n.getKind();
  Node result;

  // BV variable → fresh PBV variable (width pinned later via pbvsize=k).
  if (n.isVar() && n.getType().isBitVector())
  {
    auto it = d_bvVarPbv.find(n);
    Node pbvVar;
    if (it == d_bvVarPbv.end())
    {
      std::stringstream ss;
      ss << "pbv_" << n;
      pbvVar = NodeManager::mkDummySkolem(
          ss.str(), nm->pbvType(), "BV→PBV var",
          SkolemFlags::SKOLEM_EXACT_NAME);
      d_bvVarPbv[n] = pbvVar;
    }
    else
    {
      pbvVar = it->second;
    }
    d_liftCache[n] = pbvVar;
    return pbvVar;
  }

  // BV constant → INT_TO_PBV(k_const, val_const).
  if (k == Kind::CONST_BITVECTOR)
  {
    const BitVector& bv = n.getConst<BitVector>();
    Node wInt = nm->mkConstInt(Rational(bv.getSize()));
    Node vInt = nm->mkConstInt(Rational(bv.getValue()));
    result = nm->mkNode(Kind::INT_TO_PBV, wInt, vInt);
    d_liftCache[n] = result;
    return result;
  }

  // Lift all children first; bail if any child fails to lift.
  std::vector<Node> liftedChildren;
  liftedChildren.reserve(n.getNumChildren());
  for (const Node& c : n)
  {
    Node lc = liftBvToPbv(c);
    if (lc.isNull())
    {
      d_liftCache[n] = Node::null();
      return Node::null();
    }
    liftedChildren.push_back(lc);
  }

  // Map BV kinds to PBV kinds (binary/n-ary cases first).
  Kind pk = Kind::UNDEFINED_KIND;
  switch (k)
  {
    case Kind::BITVECTOR_AND:       pk = Kind::PBV_AND; break;
    case Kind::BITVECTOR_OR:        pk = Kind::PBV_OR; break;
    case Kind::BITVECTOR_XOR:       pk = Kind::PBV_XOR; break;
    case Kind::BITVECTOR_NOT:       pk = Kind::PBV_NOT; break;
    case Kind::BITVECTOR_ADD:       pk = Kind::PBV_ADD; break;
    case Kind::BITVECTOR_SUB:       pk = Kind::PBV_SUB; break;
    case Kind::BITVECTOR_MULT:      pk = Kind::PBV_MULT; break;
    case Kind::BITVECTOR_NEG:       pk = Kind::PBV_NEG; break;
    case Kind::BITVECTOR_UDIV:      pk = Kind::PBV_UDIV; break;
    case Kind::BITVECTOR_UREM:      pk = Kind::PBV_UREM; break;
    case Kind::BITVECTOR_SHL:       pk = Kind::PBV_SHL; break;
    case Kind::BITVECTOR_LSHR:      pk = Kind::PBV_LSHR; break;
    case Kind::BITVECTOR_ASHR:      pk = Kind::PBV_ASHR; break;
    case Kind::BITVECTOR_CONCAT:    pk = Kind::PBV_CONCAT; break;
    case Kind::BITVECTOR_ULT:       pk = Kind::PBV_ULT; break;
    case Kind::BITVECTOR_ULE:       pk = Kind::PBV_ULE; break;
    case Kind::BITVECTOR_UGT:       pk = Kind::PBV_UGT; break;
    case Kind::BITVECTOR_UGE:       pk = Kind::PBV_UGE; break;
    case Kind::BITVECTOR_SLT:       pk = Kind::PBV_SLT; break;
    case Kind::BITVECTOR_SLE:       pk = Kind::PBV_SLE; break;
    case Kind::BITVECTOR_SGT:       pk = Kind::PBV_SGT; break;
    case Kind::BITVECTOR_SGE:       pk = Kind::PBV_SGE; break;
    default: break;
  }
  if (pk != Kind::UNDEFINED_KIND)
  {
    result = nm->mkNode(pk, liftedChildren);
    d_liftCache[n] = result;
    return result;
  }

  // Indexed BV ops: rewrite the operator into PBV form (3-child / 2-child).
  if (k == Kind::BITVECTOR_EXTRACT)
  {
    const BitVectorExtract& ext = n.getOperator().getConst<BitVectorExtract>();
    result = nm->mkNode(Kind::PBV_EXTRACT,
                        liftedChildren[0],
                        nm->mkConstInt(Rational(ext.d_high)),
                        nm->mkConstInt(Rational(ext.d_low)));
    d_liftCache[n] = result;
    return result;
  }
  if (k == Kind::BITVECTOR_ZERO_EXTEND)
  {
    unsigned amt = n.getOperator().getConst<BitVectorZeroExtend>();
    result = nm->mkNode(Kind::PBV_ZERO_EXTEND,
                        nm->mkConstInt(Rational(amt)),
                        liftedChildren[0]);
    d_liftCache[n] = result;
    return result;
  }
  if (k == Kind::BITVECTOR_SIGN_EXTEND)
  {
    unsigned amt = n.getOperator().getConst<BitVectorSignExtend>();
    result = nm->mkNode(Kind::PBV_SIGN_EXTEND,
                        nm->mkConstInt(Rational(amt)),
                        liftedChildren[0]);
    d_liftCache[n] = result;
    return result;
  }

  // Any remaining bit-vector operator is one we do not lift to a PBV kind
  // (e.g. bvcomp, ultbv, the overflow predicates). BV variables and constants
  // were already handled above, so reaching here with a THEORY_BV kind means
  // the operator is unsupported. Bail with null so the caller leaves the whole
  // assertion as native BV rather than building an ill-typed PBV term (which
  // would later abort computeKappa).
  if (theory::kindToTheoryId(k) == theory::THEORY_BV)
  {
    // Overflow predicates (bvuaddo, bvsmulo, …) have no bit-blast strategy and
    // are not removed by the plain rewriter — they are expanded by
    // eliminateOverflows into basic ops (bvult, extract, concat, …) that the
    // lifter does handle. Expand and re-lift; only bail if no expansion
    // applies. (Leaving such a predicate as native BV would crash the
    // bit-blaster, since solve-bv-as-int bypasses the elimination pass.)
    Node expanded = theory::bv::TheoryBVRewriter::eliminateOverflows(n);
    if (expanded != n)
    {
      Node r = liftBvToPbv(expanded);
      d_liftCache[n] = r;
      return r;
    }
    d_liftCache[n] = Node::null();
    return Node::null();
  }

  // A child that was bit-vector-typed may have been lifted to a PBV term.
  // That is only well-typed under operators that accept the lifted form:
  //   * EQUAL / DISTINCT      — compare two PBV terms,
  //   * ITE                    — PBV-typed branches,
  //   * APPLY_UF               — handled specially by the int-blaster, which
  //                              translates both the symbol and its args.
  // Any other operator (e.g. `ubv_to_int`, which bridges BV to native Int in
  // QF_UFBVLIA) genuinely requires a bit-vector child and cannot consume a PBV
  // one. Rebuilding it would produce an ill-typed node, so bail and let the
  // caller fall back to native bit-vectors.
  if (k != Kind::EQUAL && k != Kind::DISTINCT && k != Kind::ITE
      && k != Kind::APPLY_UF)
  {
    for (const Node& c : n)
    {
      if (c.getType().isBitVector())
      {
        d_liftCache[n] = Node::null();
        return Node::null();
      }
    }
  }

  // Non-BV nodes: rebuild with lifted children (Booleans / Int / EQUAL / ITE …).
  // For leaf non-BV terms (variables, constants), this just returns n.
  if (liftedChildren.empty())
  {
    d_liftCache[n] = n;
    return n;
  }
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    std::vector<Node> withOp;
    withOp.push_back(n.getOperator());
    withOp.insert(withOp.end(), liftedChildren.begin(), liftedChildren.end());
    result = nm->mkNode(k, withOp);
  }
  else
  {
    result = nm->mkNode(k, liftedChildren);
  }
  d_liftCache[n] = result;
  return result;
}

void BVToInt::addSkolemDefinitions(const std::map<Node, Node>& skolems)
{
  map<Node, Node>::const_iterator it;
  for (it = skolems.begin(); it != skolems.end(); it++)
  {
    Node originalSkolem = it->first;
    Node definition = it->second;
    std::vector<Node> args;
    Node body;
    if (definition.getType().isFunction())
    {
      args.insert(args.end(), definition[0].begin(), definition[0].end());
      body = definition[1];
    }
    else
    {
      body = definition;
    }
    Trace("bv-to-int-debug") << "adding substitution: " << "[" << originalSkolem  << "] ----> [" << definition << "]"  << std::endl; 
    d_preprocContext->addSubstitution(originalSkolem, definition);
  }
}

void BVToInt::addFinalizeAssertions(
    AssertionPipeline* assertionsToPreprocess,
    const std::vector<TrustNode>& additionalConstraints)
{
  Trace("bv-to-int-debug") << "range constraints:" << std::endl;
  for (const TrustNode& tlem : additionalConstraints)
  {
    Trace("bv-to-int-debug") << "- " << tlem.getProven() << std::endl;
    assertionsToPreprocess->pushBackTrusted(tlem);
  }
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
