#include "theory/pbv/theory_pbv_type_rules.h"
#include "util/pbv.h"
#include "util/cardinality.h"

namespace cvc5::internal {

class NodeManager;
class TypeNode;

namespace theory {
namespace pbv {

TypeNode PbvTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}

TypeNode PbvTypeRule::computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut){
  Assert(n.getNumChildren() == 2);

  TNode arg1 = n[0];
  TNode arg2 = n[1];

  if (check)
  {    
    TypeNode t1 = arg1.getType();
    TypeNode t2 = arg2.getType();
    if (t1 != t2)
    {
      if (errOut)
      {
        *errOut << "Arguments must have same type.";
      }
      throw TypeCheckingExceptionPrivate(n, "Mismatched types in pbv");
    }
  }
  return nodeManager->pbvType();
}

TypeNode PbvPredicateTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode PbvPredicateTypeRule::computeType(NodeManager* nodeManager,
                                                 TNode n,
                                                 bool check,
                                                 std::ostream* errOut)
{
  Assert(n.getNumChildren() == 2);

  TNode arg1 = n[0];
  TNode arg2 = n[1];

  if (check)
  {    
    TypeNode t1 = arg1.getType();
    TypeNode t2 = arg2.getType();
    if (t1 != t2)
    {
      if (errOut)
      {
        *errOut << "Arguments must have same type.";
      }
      throw TypeCheckingExceptionPrivate(n, "Mismatched types in pbv");
    }
  }
  return nodeManager->booleanType();
}


}  // namespace pbv
}  // namespace theory
}  // namespace cvc5::internal