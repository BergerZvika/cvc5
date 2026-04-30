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
 * The BVToInt preprocessing pass.
 *
 * Converts bit-vector operations into integer operations.
 *
 */

#include "preprocessing/passes/pbv_to_int.h"

#include <cmath>
#include <string>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/node_traversal.h"
#include "options/smt_options.h"
#include "options/uf_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/pbv/theory_pbv_rewriter.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace std;
using namespace cvc5::internal::theory;
using namespace cvc5::internal::theory::pbv;

PBVToInt::PBVToInt(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "pbv-to-int"),
      d_intBlaster(preprocContext->getEnv()) {}

PreprocessingPassResult PBVToInt::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  // vector of boolean nodes for additional constraints
  // this will always contain range constraints
  // and for options::SolveBVAsIntMode::BITWISE, it will
  // also include bitwise assertion constraints
  std::vector<TrustNode> additionalConstraints;
  std::map<Node, Node> skolems;
  // Phase 1 — pre-scan every rewritten assertion so the int-blaster's
  // kappa union-find has global visibility before any skolem is allocated.
  // Without this, an assertion that only mentions a variable directly
  // would get its own kappa class even when a sibling assertion ties it
  // to `int_to_pbv k _`, forcing the user's `k` to be aliased to a fresh
  // skolem instead of used directly.
  for (uint64_t i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    assertionsToPreprocess->ensureRewritten(i);
    d_intBlaster.scanAssertion((*assertionsToPreprocess)[i]);
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
    Trace("pbv-to-int-debug") << "pbv node: " << bvNode << std::endl;
    Trace("pbv-to-int-debug") << "int node: " << tr.getProven()[1] << std::endl;
    assertionsToPreprocess->replaceTrusted(i, tr);
    // ensure integer rewritten
    assertionsToPreprocess->ensureRewritten(i);
  }
  addFinalizeAssertions(assertionsToPreprocess, additionalConstraints);
  addSkolemDefinitions(skolems);

  // Compact: drop any `(assert true)` left behind by translations whose
  // bodies became tautological after substitution / lemma emission. We
  // gather the surviving assertions, clear, and push them back. This loses
  // per-assertion provenance — only safe with proofs disabled.
  if (options().smt.proofMode == options::ProofMode::OFF)
  {
    std::vector<Node> kept;
    kept.reserve(assertionsToPreprocess->size());
    for (size_t i = 0; i < assertionsToPreprocess->size(); ++i)
    {
      // Rewrite once more before the boolean check — some assertions may
      // have arrived after a downstream substitution but never had
      // ensureRewritten called, so their visible form still hides a true.
      Node a = rewrite((*assertionsToPreprocess)[i]);
      if (a.isConst() && a.getType().isBoolean() && a.getConst<bool>())
      {
        continue;  // skip (assert true)
      }
      kept.push_back(a);
    }
    if (kept.size() != assertionsToPreprocess->size())
    {
      assertionsToPreprocess->clear();
      for (const Node& a : kept)
      {
        assertionsToPreprocess->push_back(a);
      }
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

void PBVToInt::addFinalizeAssertions(
    AssertionPipeline* assertionsToPreprocess,
    const std::vector<TrustNode>& additionalConstraints)
{
  for (const TrustNode& tlem : additionalConstraints)
  {
    Trace("pbv-to-int-debug") << "- " << tlem.getProven() << std::endl;
    // ensureRew=true: rewrite the lemma immediately on push so later
    // compaction can drop any that simplify to `true`.
    assertionsToPreprocess->pushBackTrusted(
        tlem, TrustId::UNKNOWN_PREPROCESS_LEMMA, /*ensureRew=*/true);
  }
}

void PBVToInt::addSkolemDefinitions(const std::map<Node, Node>& skolems)
{
  for (const auto& [orig, def] : skolems)
  {
    // Keep PBV-typed back-definitions (`s : PBitVec  ⇒  int_to_pbv κ χ(s)`)
    // so the model engine can recover (get-value s) from the integer
    // skolems χ and κ. TheoryPbv::collectModelValues unwraps this form into
    // a CONST_PBV `(_ pbv <val> <width>)` constant.
    Trace("pbv-to-int-debug")
        << "adding substitution: [" << orig << "] ----> [" << def << "]"
        << std::endl;
    d_preprocContext->addSubstitution(orig, def);
  }
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
