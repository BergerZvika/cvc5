/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::ArrayStoreAll.
 */

#include "expr/array_store_all.h"
#include "test_smt.h"
#include "util/rational.h"
#include "util/uninterpreted_sort_value.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace test {

class TestUtilWhiteArrayStoreAll : public TestSmt
{
};

TEST_F(TestUtilWhiteArrayStoreAll, store_all)
{
  TypeNode usort = d_nodeManager->mkSort("U");
  ArrayStoreAll(d_nodeManager->mkArrayType(d_nodeManager->integerType(),
                                           d_nodeManager->realType()),
                d_nodeManager->mkConst(CONST_RATIONAL, Rational(9, 2)));
  ArrayStoreAll(d_nodeManager->mkArrayType(d_nodeManager->mkSort("U"), usort),
                d_nodeManager->mkConst(UninterpretedSortValue(usort, 0)));
  ArrayStoreAll(d_nodeManager->mkArrayType(d_nodeManager->mkBitVectorType(8),
                                           d_nodeManager->realType()),
                d_nodeManager->mkConst(CONST_RATIONAL, Rational(0)));
  ArrayStoreAll(d_nodeManager->mkArrayType(d_nodeManager->mkBitVectorType(8),
                                           d_nodeManager->integerType()),
                d_nodeManager->mkConst(CONST_RATIONAL, Rational(0)));
}

TEST_F(TestUtilWhiteArrayStoreAll, type_errors)
{
  ASSERT_THROW(ArrayStoreAll(d_nodeManager->integerType(),
                             d_nodeManager->mkConst(UninterpretedSortValue(
                                 d_nodeManager->mkSort("U"), 0))),
               IllegalArgumentException);
  ASSERT_THROW(
      ArrayStoreAll(d_nodeManager->integerType(),
                    d_nodeManager->mkConst(CONST_RATIONAL, Rational(9, 2))),
      IllegalArgumentException);
  ASSERT_THROW(
      ArrayStoreAll(d_nodeManager->mkArrayType(d_nodeManager->integerType(),
                                               d_nodeManager->mkSort("U")),
                    d_nodeManager->mkConst(CONST_RATIONAL, Rational(9, 2))),
      IllegalArgumentException);
}

TEST_F(TestUtilWhiteArrayStoreAll, const_error)
{
  TypeNode usort = d_nodeManager->mkSort("U");
  ASSERT_THROW(ArrayStoreAll(d_nodeManager->mkArrayType(
                                 d_nodeManager->mkSort("U"), usort),
                             d_nodeManager->mkVar(usort)),
               IllegalArgumentException);
  ASSERT_THROW(
      ArrayStoreAll(d_nodeManager->integerType(),
                    d_nodeManager->mkVar("x", d_nodeManager->integerType())),
      IllegalArgumentException);
  ASSERT_THROW(
      ArrayStoreAll(d_nodeManager->integerType(),
                    d_nodeManager->mkNode(
                        kind::ADD,
                        d_nodeManager->mkConst(CONST_RATIONAL, Rational(1)),
                        d_nodeManager->mkConst(CONST_RATIONAL, Rational(0)))),
      IllegalArgumentException);
}
}  // namespace test
}  // namespace cvc5::internal
