#include "theory/pbv/theory_pbv.h"

#include "theory/ee_setup_info.h"
#include "theory/pbv/theory_pbv_utils.h"
#include "theory/theory_model.h"
#include "theory/uf/equality_engine.h"
#include "util/pbv.h"
#include "util/rational.h"



namespace cvc5::internal {
namespace theory {
namespace pbv {

TheoryPbv::TheoryPbv(Env& env,
                     OutputChannel& out,
                     Valuation valuation,
                     std::string name)
    : Theory(THEORY_PBV, env, out, valuation, name),
    d_intBlaster(env),
    d_rewriter(nodeManager()),
    d_state(env, valuation),
    d_im(env, *this, d_state, "theory::pbv::"),
    d_notify(d_im)
{
  d_theoryState = &d_state;
}

TheoryPbv::~TheoryPbv() {}

TheoryRewriter* TheoryPbv::getTheoryRewriter() { return &d_rewriter; }

bool TheoryPbv::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = "theory::pbv::ee";
  return true;
}

void TheoryPbv::finishInit()
{
  Assert(d_equalityEngine != nullptr);
  eq::EqualityEngine* ee = getEqualityEngine();
  if (ee)
  {
  //    ee->addFunctionKind(Kind::BITVECTOR_AND);
  }
}

TrustNode TheoryPbv::explain(TNode n) {
  // The PBV theory does not propagate any of its own facts (it only adds
  // terms to the equality engine). If the engine still asks us to explain
  // a propagation, return a self-justifying trust node with `true` as the
  // explanation rather than a null TrustNode — a null one segfaults
  // downstream in TheoryEngine::getExplanation when getNode() is called.
  return TrustNode::mkTrustPropExp(n, nodeManager()->mkConst(true));
}

void TheoryPbv::preRegisterTerm(TNode node)
{
  eq::EqualityEngine* ee = getEqualityEngine();
  if (ee)
  {
    if (node.getKind() == Kind::EQUAL)
    {
      d_state.addEqualityEngineTriggerPredicate(node);
    }
    else
    {
      ee->addTerm(node);
    }
  }
}

bool TheoryPbv::needsCheckLastEffort() {
  return false;
}

TrustNode TheoryPbv::ppRewrite(TNode t, std::vector<SkolemLemma>& lems)
{
  return TrustNode::null();
}

bool TheoryPbv::collectModelValues(TheoryModel* m,
                                   const std::set<Node>& termSet)
{
  // For every PBV-sorted term in the relevant set, compute a concrete
  // (_ pbv <value> <width>) constant from the int-blaster's chi (integer
  // value skolem) and kappa (bit-width skolem), and assert it into the
  // model so that (get-value t) returns it.
  NodeManager* nm = nodeManager();
  for (const Node& t : termSet)
  {
    if (!t.getType().isPbv())
    {
      continue;
    }
    if (m->hasTerm(t) && m->getRepresentative(t).isConst())
    {
      // already assigned by another theory
      continue;
    }
    // Locate the chi (integer value) and kappa (integer width) skolems.
    // Try the int-blaster's maps first; if absent (e.g. the original PBV
    // variable was substituted away to INT_TO_PBV(k, v)), fall back to
    // evaluating `t` and unpacking that wrapper.
    Node chi   = d_intBlaster.lookupChi(t);
    Node kappa = d_intBlaster.lookupKappa(t);
    if (chi.isNull() || kappa.isNull())
    {
      Node tVal = m->getValue(t);
      if (!tVal.isNull() && tVal.getKind() == Kind::INT_TO_PBV
          && tVal.getNumChildren() == 2)
      {
        if (kappa.isNull()) kappa = tVal[0];
        if (chi.isNull())   chi   = tVal[1];
      }
    }
    Integer val(0), size(0);
    if (!chi.isNull())
    {
      Node chiVal = m->getValue(chi);
      if (chiVal.isConst() && chiVal.getType().isInteger())
      {
        val = chiVal.getConst<Rational>().getNumerator();
      }
    }
    if (!kappa.isNull())
    {
      Node kVal = m->getValue(kappa);
      if (kVal.isConst() && kVal.getType().isInteger())
      {
        size = kVal.getConst<Rational>().getNumerator();
      }
    }
    Node pbvConst = nm->mkConst(Kind::CONST_PBV, Pbv(val, size));
    if (!m->assertEquality(t, pbvConst, true))
    {
      return false;
    }
  }
  return true;
}

}  // namespace pbv
}  // namespace theory
}  // namespace cvc5::internal