#include "theory/pbv/theory_pbv.h"
#include "theory/ee_setup_info.h"
#include "theory/uf/equality_engine.h"



namespace cvc5::internal {
namespace theory {
namespace pbv {

TheoryPbv::TheoryPbv(Env& env,
                     OutputChannel& out,
                     Valuation valuation,
                     std::string name)
    : Theory(THEORY_PBV, env, out, valuation, name),
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

TrustNode TheoryPbv::explain(TNode) {
//   std::cout << "explain\n";
  return TrustNode();
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
//   if (d_lastEffortCalled) {
//     return false;
//   }
//   d_lastEffortCalled = true;
//   presolve();
  return false;
}


}  // namespace pbv
}  // namespace theory
}  // namespace cvc5::internal