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
 * Util functions for theory PBV.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__PBV__THEORY_BV_UTILS_H
#define CVC5__THEORY__PBV__THEORY_BV_UTILS_H

#include "expr/node_manager.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace theory {
namespace pbv {
namespace utils {

/* Create parametric bit-vector constant of given size and value. */
Node mkConst(NodeManager* nm, unsigned int value);
Node mkConst(NodeManager* nm, Integer& value);
/* Create bit-vector constant from given bit-vector. */
// Node mkConst(NodeManager* nm, const BitVector& value);

} // namespace utils

}  // namespace pbv
}  // namespace theory
}  // namespace cvc5::internal

#endif

