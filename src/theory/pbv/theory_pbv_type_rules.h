#include "cvc5_private.h"

#ifndef CVC5__THEORY__PBV__THEORY_PBV_TYPE_RULES_H
#define CVC5__THEORY__PBV__THEORY_PBV_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5::internal {
namespace theory {
namespace pbv {

/* -------------------------------------------------------------------------- */

struct PbvTypeRule {
  /**
   * Type rule for PBV operators.
   */
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/* -------------------------------------------------------------------------- */

class PbvPredicateTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/* -------------------------------------------------------------------------- */


// struct PbvOpTypeRule {
  /**
   * Type rule for generic PBV operators.
   * Ensures all children are of type PBV.
   */
//   static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
//     TypeNode pbvType = nodeManager->mkTypeConst(TYPE_PBV); // Assuming generated enum

//     if (check) {
//       for (const auto& child : n) {
//         TypeNode childType = child.getType(check);
//         if (childType != pbvType) {
//            // In a real implementation, throw a TypeCheckingExceptionPrivate here
//            // For now, we assume it matches or handle error
//         }
//       }
//     }
//     return pbvType;
//   }
// };

}  // namespace pbv
}  // namespace theory
}  // namespace cvc5::internal

#endif