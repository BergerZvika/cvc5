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
 * An enumerator for bitvectors.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__PBV__TYPE_ENUMERATOR_H
#define CVC5__THEORY__PBV__TYPE_ENUMERATOR_H

#include "expr/kind.h"
#include "expr/type_node.h"
#include "theory/type_enumerator.h"
#include "util/integer.h"
#include "theory/pbv/theory_pbv_utils.h"

namespace cvc5::internal {
namespace theory {
namespace pbv {

class ParametricBitVectorEnumerator : public TypeEnumeratorBase<ParametricBitVectorEnumerator> {
  Integer d_bits;

public:

  ParametricBitVectorEnumerator(TypeNode type, TypeEnumeratorProperties * tep = NULL) :
    TypeEnumeratorBase<ParametricBitVectorEnumerator>(type),
    d_bits(0) {
  }

  Node operator*() override
  {
    return utils::mkConst(getType().getNodeManager(), d_bits);
  }

  ParametricBitVectorEnumerator& operator++() override
  {
    d_bits += 1;
    return *this;
  }

  bool isFinished() override { return false; }
};/* ParametricBitVectorEnumerator */

}  // namespace pbv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__PBV__TYPE_ENUMERATOR_H */
