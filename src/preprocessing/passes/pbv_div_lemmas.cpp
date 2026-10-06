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
 * Instances of unsigned-division identities for PBV terms.
 */

#include "preprocessing/passes/pbv_div_lemmas.h"

#include <unordered_set>
#include <vector>

#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/rewriter.h"
#include "util/rational.h"
#include "util/statistics_registry.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

PbvDivLemmas::PbvDivLemmas(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "pbv-div-lemmas"),
      d_stats(statisticsRegistry())
{
}

PbvDivLemmas::Statistics::Statistics(StatisticsRegistry& reg)
    : d_numNested(
        reg.registerInt("preprocessing::passes::PbvDivLemmas::NumNested")),
      d_numCancel(
          reg.registerInt("preprocessing::passes::PbvDivLemmas::NumCancel"))
{
}

PreprocessingPassResult PbvDivLemmas::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager* nm = nodeManager();
  Node zeroInt = nm->mkConstInt(Rational(0));
  Node oneInt = nm->mkConstInt(Rational(1));
  Node twoInt = nm->mkConstInt(Rational(2));

  // every pbvudiv term of the assertions
  std::unordered_set<Node> divs;
  std::unordered_set<TNode> visited;
  std::vector<TNode> stack(assertionsToPreprocess->begin(),
                           assertionsToPreprocess->end());
  while (!stack.empty())
  {
    TNode n = stack.back();
    stack.pop_back();
    if (!visited.insert(n).second) continue;
    if (n.getKind() == Kind::PBV_UDIV) divs.insert(n);
    stack.insert(stack.end(), n.begin(), n.end());
  }
  if (divs.empty())
  {
    return PreprocessingPassResult::NO_CONFLICT;
  }

  auto zeroOf = [&](Node t) {
    return nm->mkNode(
        Kind::INT_TO_PBV, nm->mkNode(Kind::PBV_SIZE, t), zeroInt);
  };
  auto nonZero = [&](Node t) { return t.eqNode(zeroOf(t)).notNode(); };
  // extract(zext(p) * zext(q), 2w-1, w) = 0 with w the width of p
  auto noOverflow = [&](Node p, Node q) {
    Node w = nm->mkNode(Kind::PBV_SIZE, p);
    Node prod = nm->mkNode(Kind::PBV_MULT,
                           nm->mkNode(Kind::PBV_ZERO_EXTEND, w, p),
                           nm->mkNode(Kind::PBV_ZERO_EXTEND, w, q));
    Node hi = nm->mkNode(
        Kind::SUB, nm->mkNode(Kind::MULT, twoInt, w), oneInt);
    return nm->mkNode(Kind::PBV_EXTRACT, prod, hi, w).eqNode(zeroOf(p));
  };
  auto has = [&](Node t) { return divs.find(t) != divs.end(); };

  std::vector<Node> lemmas;
  for (const Node& u : divs)
  {
    Node num = u[0], den = u[1];
    // (D1) (x / a) / b = x / (a * b)
    if (num.getKind() == Kind::PBV_UDIV)
    {
      Node x = num[0], a = num[1], b = den;
      for (const Node& m : {nm->mkNode(Kind::PBV_MULT, a, b),
                            nm->mkNode(Kind::PBV_MULT, b, a)})
      {
        Node v = nm->mkNode(Kind::PBV_UDIV, x, m);
        if (!has(v)) continue;
        Node prem = nm->mkNode(
            Kind::AND, noOverflow(a, b), nonZero(a), nonZero(b));
        lemmas.push_back(prem.impNode(u.eqNode(v)));
        ++d_stats.d_numNested;
        break;
      }
    }
    // (D2) (x * a) / c = x / (c / a)
    if (num.getKind() == Kind::PBV_MULT && num.getNumChildren() == 2)
    {
      Node c = den;
      for (size_t i = 0; i < 2; ++i)
      {
        Node x = num[i], a = num[1 - i];
        Node v = nm->mkNode(
            Kind::PBV_UDIV, x, nm->mkNode(Kind::PBV_UDIV, c, a));
        if (!has(v)) continue;
        Node prem = nm->mkNode(
            Kind::AND,
            noOverflow(x, a),
            nm->mkNode(Kind::PBV_UREM, c, a).eqNode(zeroOf(c)),
            nonZero(c));
        lemmas.push_back(prem.impNode(u.eqNode(v)));
        ++d_stats.d_numCancel;
        break;
      }
    }
  }
  for (const Node& l : lemmas)
  {
    Trace("pbv-div-lemmas") << "lemma: " << l << std::endl;
    assertionsToPreprocess->push_back(rewrite(l));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
