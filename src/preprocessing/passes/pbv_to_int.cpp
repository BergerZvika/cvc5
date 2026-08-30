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
#include "options/base_options.h"
#include "options/smt_options.h"
#include "options/uf_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "expr/node_algorithm.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/logic_exception.h"
#include "theory/pbv/theory_pbv_rewriter.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"

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
  // Harvest the width constraints before translation; see d_widthAssertions.
  if (options().smt.pbvTypeCheck == options::PbvTypeCheckMode::DEEP_BEFORE
      || options().smt.pbvTypeCheck == options::PbvTypeCheckMode::DEEP_AFTER)
  {
    for (uint64_t i = 0; i < assertionsToPreprocess->size(); ++i)
    {
      Node a = (*assertionsToPreprocess)[i];
      if (isWidthOnly(a))
      {
        d_widthAssertions.push_back(a);
      }
    }
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

  // Type checking (opt-in). Runs on the translated assertions, where widths
  // are ordinary Int symbols, so the query is a plain arithmetic formula.
  if (options().smt.pbvTypeCheck != options::PbvTypeCheckMode::NONE)
  {
    typeCheck(assertionsToPreprocess);
  }

  // Post-pass on the NIA formula (opt-in): delete redundant `mod 2^k`.
  if (options().smt.pbvToIntReduceMods != options::PbvReduceModsMode::NONE)
  {
    reduceRedundantPow2Mods(assertionsToPreprocess);
  }

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

bool PBVToInt::isWidthOnly(TNode n)
{
  // A width constraint mentions PBV terms only as the argument of `pbvsize`,
  // AND actually mentions a width: without the second requirement every
  // PBV-free assertion would qualify, so in a problem with no parametric
  // bit-vectors at all the whole formula would be taken for a width query.
  bool sawSize = false;
  std::vector<TNode> toVisit{n};
  std::unordered_set<TNode> visited;
  while (!toVisit.empty())
  {
    TNode cur = toVisit.back();
    toVisit.pop_back();
    if (!visited.insert(cur).second)
    {
      continue;
    }
    if (cur.getKind() == Kind::PBV_SIZE)
    {
      // Its argument may be an arbitrary PBV term; the width of that term is
      // still a width, so do not descend into it.
      sawSize = true;
      continue;
    }
    if (cur.getType().isPbv())
    {
      return false;
    }
    for (TNode c : cur)
    {
      toVisit.push_back(c);
    }
  }
  return sawSize;
}

Node PBVToInt::buildTypeCheckQuery(AssertionPipeline* assertionsToPreprocess,
                                   bool deep)
{
  NodeManager* nm = nodeManager();
  std::vector<Node> conj;
  // Shallow: the admissibility constraint Adm(phi), i.e. the local width side
  // conditions of each sub-term. Linear, and decidable.
  for (const Node& a : d_intBlaster.getAdmConstraints())
  {
    // Only a trivially TRUE constraint is dropped. A constant `false` here is
    // the ill-typedness itself -- an equal-width requirement between two
    // pinned widths, say 3 = 5, rewrites to false -- and every Adm constraint
    // is about widths by construction, so keeping it cannot misattribute a
    // bit-vector contradiction to typing.
    if (a.isConst() && a.getType().isBoolean() && a.getConst<bool>())
    {
      continue;
    }
    conj.push_back(a);
  }
  if (deep)
  {
    // Deep: additionally every constraint on widths that the formula itself
    // imposes, taken from the pre-translation harvest and mapped into the
    // kappa language. Everything else about the formula is dropped, which only
    // adds models, so an unsatisfiable verdict remains conclusive.
    for (const Node& w : d_widthAssertions)
    {
      Node nw = d_intBlaster.toWidthTerm(w);
      if (!nw.isNull() && !(nw.isConst() && nw.getConst<bool>()))
      {
        conj.push_back(nw);
      }
    }
  }
  if (conj.empty())
  {
    return nm->mkConst(true);
  }
  return conj.size() == 1 ? conj[0] : nm->mkNode(Kind::AND, conj);
}

void PBVToInt::typeCheck(AssertionPipeline* assertionsToPreprocess)
{
  using Mode = options::PbvTypeCheckMode;
  Mode mode = options().smt.pbvTypeCheck;
  const bool deep =
      mode == Mode::DEEP_BEFORE || mode == Mode::DEEP_AFTER;
  const bool before =
      mode == Mode::SHALLOW_BEFORE || mode == Mode::DEEP_BEFORE;

  Node query = buildTypeCheckQuery(assertionsToPreprocess, deep);
  Trace("pbv-type-check") << "PBVToInt::typeCheck: " << (deep ? "deep" : "shallow")
                          << " query " << query << std::endl;
  if (isOutputOn(OutputTag::PBV_TYPE_CHECK))
  {
    output(OutputTag::PBV_TYPE_CHECK)
        << "(pbv-type-check :checker " << (deep ? "deep" : "shallow")
        << " :when " << (before ? "before" : "after") << std::endl
        << "  :query " << query << ")" << std::endl;
  }
  if (!before)
  {
    // Diagnostic mode: the query is only worth solving once the main solve
    // has answered unsat, so hand it over and leave the assertions alone.
    d_preprocContext->setPbvTypeCheckQuery(query);
    return;
  }
  if (query.isConst() && query.getConst<bool>())
  {
    return;  // nothing to discharge
  }
  // A separate, width-only obligation discharged ahead of the main solve, in
  // the manner of the type correctness conditions of CVC Lite: if it fails,
  // no assignment to the widths makes the formula well-sorted, and no
  // bit-vector reasoning is needed to know the formula is unsatisfiable.
  // The subsolver must not itself type check: its query is an ordinary
  // arithmetic formula, and re-entering here would recurse without end.
  Options subOpts;
  subOpts.copyValues(options());
  subOpts.write_smt().pbvTypeCheck = options::PbvTypeCheckMode::NONE;
  theory::SubsolverSetupInfo ssi(d_preprocContext->getEnv(), subOpts);
  Result r = theory::checkWithSubsolver(query, ssi);
  Trace("pbv-type-check") << "PBVToInt::typeCheck: verdict " << r << std::endl;
  if (isOutputOn(OutputTag::PBV_TYPE_CHECK))
  {
    output(OutputTag::PBV_TYPE_CHECK)
        << "(pbv-type-check :verdict " << r << ")" << std::endl;
  }
  if (r.getStatus() == Result::UNSAT)
  {
    // The formula is ill-typed: no assignment to the symbolic widths makes it
    // well-sorted. Raise rather than answering unsat, so that the caller
    // cannot mistake a typing failure for a bit-vector one -- which is the
    // whole point of running the checker.
    std::stringstream ss;
    ss << "PBV type checking (--pbv-type-check="
       << (deep ? "deep-before" : "shallow-before")
       << ") rejected this formula: no assignment to the symbolic widths "
          "makes it well-sorted. The "
       << (deep ? "deep" : "shallow")
       << " width query is unsatisfiable.";
    throw LogicException(ss.str());
  }
}

void PBVToInt::reduceRedundantPow2Mods(
    AssertionPipeline* assertionsToPreprocess)
{
  Pow2ModReducer reducer(d_preprocContext->getEnv());

  // Phase 1 — harvest width-ordering facts from the whole assertion set. The
  // ADM/RANGE lemmas pushed by addFinalizeAssertions are already in here, so
  // `i < kappa(t)` and `kappa > 0` are available alongside the user's own
  // width constraints.
  std::vector<Node> all;
  all.reserve(assertionsToPreprocess->size());
  for (size_t i = 0, sz = assertionsToPreprocess->size(); i < sz; ++i)
  {
    all.push_back((*assertionsToPreprocess)[i]);
  }
  reducer.harvest(all);

  // Phase 2 — delete redundant mods.
  for (size_t i = 0, sz = assertionsToPreprocess->size(); i < sz; ++i)
  {
    Node before = (*assertionsToPreprocess)[i];
    Node after = reducer.reduce(before);
    if (after != before)
    {
      assertionsToPreprocess->replace(i, after);
      assertionsToPreprocess->ensureRewritten(i);
    }
  }
  if (getenv("PBV_DEBUG_REDUCER") != nullptr)
  {
    std::cerr << "[reduce-mods] removed " << reducer.numRemoved() << " mod(s):";
    for (const auto& [c, n] : reducer.caseCounts())
    {
      std::cerr << " case" << c << "=" << n;
    }
    std::cerr << std::endl;
  }
  Trace("pbv-to-int") << "pbv-to-int-reduce-mods: removed "
                      << reducer.numRemoved() << " mod(s)";
  for (const auto& [c, n] : reducer.caseCounts())
  {
    Trace("pbv-to-int") << "  case" << c << "=" << n;
  }
  Trace("pbv-to-int") << std::endl;
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
