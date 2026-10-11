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
 * learned-rewrite-pbv: the conditional multi-width PBV rewrites.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__LEARNED_REWRITE_PBV_H
#define CVC5__PREPROCESSING__PASSES__LEARNED_REWRITE_PBV_H

#include "preprocessing/passes/pbv_mw.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * The PBV half of the learned rewrites: every multi-width rule whose side
 * condition is decided against facts -- the order facts of the assertions
 * (with the pinned admissibility constraints), the width aliases, harvested
 * `z <u m` bounds and mask facts, and the learned literals of non-clausal
 * simplification when there are any. Selected by the PBV tokens of
 * --learned-rewrite-rules.
 *
 * Runs before pbv-to-int, INSTEAD of pbv-mw: it is the same engine, with the
 * unconditional families that pbv-mw would run switched on as well, so the
 * two kinds of rule reach the common fixed point they reached when they
 * were one pass.
 */
class LearnedRewritePbv : public PbvMw
{
 public:
  LearnedRewritePbv(PreprocessingPassContext* preprocContext);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__LEARNED_REWRITE_PBV_H */
