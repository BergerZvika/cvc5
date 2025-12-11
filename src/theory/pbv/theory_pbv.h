#include "cvc5_private.h"

#ifndef CVC5__THEORY__PBV__THEORY_PBV_H
#define CVC5__THEORY__PBV__THEORY_PBV_H

#include "theory/pbv/theory_pbv_rewriter.h"
#include "theory/theory.h"
#include "theory/theory_eq_notify.h"
#include "theory/theory_state.h"


namespace cvc5::internal {
namespace theory {
namespace pbv {

class TheoryPbv : public Theory {
 public:
  TheoryPbv(Env& env,
           OutputChannel& out,
           Valuation valuation,
           std::string name = "");

  ~TheoryPbv();

  //--------------------------------- initialization
  /** get the official theory rewriter of this theory */
  TheoryRewriter* getTheoryRewriter() override;
  /** get the proof checker of this theory */
  ProofRuleChecker* getProofChecker() override {}

    /**
   * Returns true if we need an equality engine. If so, we initialize the
   * information regarding how it should be setup. For details, see the
   * documentation in Theory::needsEqualityEngine.
   */
  bool needsEqualityEngine(EeSetupInfo& esi) override;

  void finishInit() override;
  //--------------------------------- end initialization
  std::string identify() const override { return std::string("TheoryPbv"); }
  
  TrustNode explain(TNode n) override;

  void presolve() override {}

  void preRegisterTerm(TNode n) override;
  //--------------------------------- standard check
  bool needsCheckLastEffort() override;

  // bool preNotifyFact(TNode atom,
  //                    bool pol,
  //                    TNode fact,
  //                    bool isPrereg,
  //                    bool isInternal) override {}

  // void notifyFact(TNode atom, bool pol, TNode fact, bool isInternal) override {}
  // bool preCheck(Effort e) override {}
  // void postCheck(Effort e) override  {}
  //--------------------------------- end standard check
  // TrustNode ppRewrite(TNode t, std::vector<SkolemLemma>& lems) override {}

  TrustNode ppStaticRewrite(TNode atom) override { return TrustNode::null(); }

  /** Collect model values in m based on the relevant terms given by termSet */
  // bool collectModelValues(TheoryModel* m,
                          // const std::set<Node>& termSet) override { }

  // void propagate(Effort e) override {}

  // void computeRelevantTerms(std::set<Node>& termSet) override {}



  // bool ppAssert(TrustNode in, TrustSubstitutionMap& outSubstitutions) override {}

  // void ppStaticLearn(TNode in, std::vector<TrustNode>& learned) override {}

  // EqualityStatus getEqualityStatus(TNode a, TNode b) override {}
 private:
  // void notifySharedTerm(TNode t) override {}

   /** The theory rewriter for this theory. */
  TheoryPbvRewriter d_rewriter;

  /** A (default) theory state object */
  TheoryState d_state;

  /** A (default) theory inference manager. */
  TheoryInferenceManager d_im;

  /** The notify class for equality engine. */
  TheoryEqNotifyClass d_notify;
};

}  // namespace pbv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__PBV__THEORY_PBV_H */