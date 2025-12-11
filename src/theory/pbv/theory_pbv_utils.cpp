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
 * Util functions for theory BV.
 */

 #include "theory/pbv/theory_pbv_utils.h"

#include "options/theory_options.h"
#include "theory/theory.h"

using namespace cvc5::internal::kind;


namespace cvc5::internal {
namespace theory {
namespace pbv {
namespace utils {
    
/* ------------------------------------------------------------------------- */

Node mkConst(NodeManager* nm, unsigned int value) {}
Node mkConst(NodeManager* nm, Integer& value) {}
/* ------------------------------------------------------------------------- */


}  // namespace utils
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal