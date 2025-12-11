#include "cvc5_private.h"

#ifndef CVC5__THEORY__PBV__THEORY_PBV_REWRITER_H
#define CVC5__THEORY__PBV__THEORY_PBV_REWRITER_H

#include "theory/theory_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace pbv {

typedef RewriteResponse (*RewriteFunction) (TNode, bool);

class TheoryPbvRewriter : public TheoryRewriter {
 public:
  TheoryPbvRewriter(NodeManager* nm) : TheoryRewriter(nm) {}
  /**
   * Rewrite a node into a normal form.
   * For now, simply returns the original node (REWRITE_DONE).
   */
  RewriteResponse postRewrite(TNode node) override {
    return RewriteResponse(REWRITE_DONE, node);
  }

  /**
   * Pre-rewrite check.
   * Also returns the original node for now.
   */
  RewriteResponse preRewrite(TNode node) override {
    return RewriteResponse(REWRITE_DONE, node);
  }
};

}  // namespace pbv
}  // namespace theory
}  // namespace cvc5::internal

#endif