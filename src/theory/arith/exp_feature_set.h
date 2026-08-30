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
 * Comma-separated feature selection for --arith-exp-rewrites and
 * --arith-exp-lemmas.
 *
 * Both options used to be single-choice enums, so a run could enable exactly
 * one schema or lemma family (or a fixed aggregate such as 'all').  They are
 * now free-form lists, so any subset can be combined:
 *
 *   --arith-exp-rewrites=unroll,const
 *   --arith-exp-lemmas=interpolation,prime
 *
 * Every previously valid single value still parses and means the same thing,
 * so existing command lines are unaffected.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__EXP_FEATURE_SET_H
#define CVC5__THEORY__ARITH__EXP_FEATURE_SET_H

#include <set>
#include <string>

namespace cvc5::internal {
namespace theory {
namespace arith {

/**
 * A parsed --arith-exp-rewrites / --arith-exp-lemmas value: the set of
 * feature names the user selected, plus the aggregates they imply.
 */
class ExpFeatureSet
{
 public:
  ExpFeatureSet() = default;
  /** Parse a comma/space-separated list. Unknown tokens are kept as-is so a
   * typo simply never matches rather than silently enabling something. */
  explicit ExpFeatureSet(const std::string& spec);

  /** Is `name` selected, either directly or via an aggregate? */
  bool has(const std::string& name) const;
  /** Was an aggregate ('all' / 'all-lemmas') given? */
  bool hasAll() const { return d_all; }
  /** True when nothing at all was selected. */
  bool empty() const { return d_names.empty() && !d_all; }

 private:
  std::set<std::string> d_names;
  /** 'all' was given: every feature is on. */
  bool d_all = false;
  /** 'all-lemmas' was given: the five SwInE families are on. */
  bool d_allLemmas = false;
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__EXP_FEATURE_SET_H */
