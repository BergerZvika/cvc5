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
 * Unit tests for the PBV int-blaster (TRANS / CONV pipeline, Section 4.2).
 *
 * Test plan
 * ---------
 * 1. translateNoChildren — CONST_PBV, PBV variables, Int variables
 * 2. computeKappa         — variables and structural terms (Algorithm 2)
 * 3. translateWithChildren — every Algorithm-3 operator (type + kind checks)
 * 4. Range constraints    — RANGE(φ): 0 ≤ χ(x) ∧ χ(x) < pow2(κ(x))
 * 5. Adm constraints      — ADM(φ): κ(x)>0, equal-width equalities
 * 6. End-to-end           — trustedIntBlast on a small formula
 */

#include <iostream>
#include <map>
#include <memory>
#include <vector>

#include "context/context.h"
#include "options/options.h"
#include "test_smt.h"
#include "theory/pbv/int_blaster.h"
#include "util/pbv.h"
#include "util/rational.h"

namespace cvc5::internal {

using namespace kind;
using namespace theory;

namespace test {

// ============================================================================
// Test fixture
// ============================================================================

class TestTheoryWhitePbvIntblaster : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_slvEngine->setOption("produce-models", "true");
    d_slvEngine->finishInit();
  }

  // Convenience: create a free PBV variable named 'name'
  Node mkPbvVar(const std::string& name)
  {
    return d_nodeManager->mkVar(name, d_nodeManager->pbvType());
  }

  // Convenience: create a free Int variable named 'name'
  Node mkIntVar(const std::string& name)
  {
    return d_nodeManager->mkVar(name, d_nodeManager->integerType());
  }

  // Convenience: integer constant
  Node mkInt(int n)
  {
    return d_nodeManager->mkConstInt(Rational(n));
  }

  // Convenience: CONST_PBV with the given integer value
  Node mkPbvConst(int v)
  {
    return d_nodeManager->mkConst(Pbv(Integer(v)));
  }
};

// ============================================================================
// 1. translateNoChildren
// ============================================================================

TEST_F(TestTheoryWhitePbvIntblaster, noChildren_pbv_constant)
{
  Env& env = d_slvEngine->getEnv();
  std::vector<TrustNode> lemmas;
  std::map<Node, Node>   skolems;
  PIntBlaster blaster(env);

  // CONST_PBV(5) should translate to the integer constant 5
  Node pbv5   = mkPbvConst(5);
  Node result = blaster.translateNoChildren(pbv5, lemmas, skolems);
  ASSERT_TRUE(result.getType().isInteger());
  ASSERT_EQ(result, mkInt(5));

  // CONST_PBV(0) → 0
  Node pbv0 = mkPbvConst(0);
  result    = blaster.translateNoChildren(pbv0, lemmas, skolems);
  ASSERT_EQ(result, mkInt(0));
}

TEST_F(TestTheoryWhitePbvIntblaster, noChildren_pbv_variable)
{
  Env& env = d_slvEngine->getEnv();
  std::vector<TrustNode> lemmas;
  std::map<Node, Node>   skolems;
  PIntBlaster blaster(env);

  // A free PBV variable should translate to a fresh Int variable χ(x)
  Node x      = mkPbvVar("x");
  Node chi_x  = blaster.translateNoChildren(x, lemmas, skolems);
  ASSERT_TRUE(chi_x.isVar());
  ASSERT_TRUE(chi_x.getType().isInteger());

  // Same variable always maps to the same χ
  Node chi_x2 = blaster.translateNoChildren(x, lemmas, skolems);
  ASSERT_EQ(chi_x, chi_x2);

  // Two distinct PBV variables should map to distinct χ values
  Node y     = mkPbvVar("y");
  Node chi_y = blaster.translateNoChildren(y, lemmas, skolems);
  ASSERT_NE(chi_x, chi_y);

  // A skolem entry x → INT_TO_PBV(κ(x), χ(x)) should have been registered
  ASSERT_TRUE(skolems.count(x) > 0);
  ASSERT_EQ(skolems[x].getKind(), Kind::INT_TO_PBV);
}

TEST_F(TestTheoryWhitePbvIntblaster, noChildren_int_variable_unchanged)
{
  Env& env = d_slvEngine->getEnv();
  std::vector<TrustNode> lemmas;
  std::map<Node, Node>   skolems;
  PIntBlaster blaster(env);

  // An Int variable should pass through unchanged
  Node n      = mkIntVar("n");
  Node result = blaster.translateNoChildren(n, lemmas, skolems);
  ASSERT_EQ(result, n);
}

// ============================================================================
// 2. computeKappa — BW function (Algorithm 2)
// ============================================================================

TEST_F(TestTheoryWhitePbvIntblaster, computeKappa_variable)
{
  Env& env = d_slvEngine->getEnv();
  PIntBlaster blaster(env);

  // κ(x) for a PBV variable: fresh Int skolem
  Node x      = mkPbvVar("x");
  Node kappa1 = blaster.computeKappa(x);
  ASSERT_TRUE(kappa1.getType().isInteger());

  // κ(x) is stable (same result on second call)
  Node kappa2 = blaster.computeKappa(x);
  ASSERT_EQ(kappa1, kappa2);

  // κ(y) ≠ κ(x) for a different variable
  Node y       = mkPbvVar("y");
  Node kappa_y = blaster.computeKappa(y);
  ASSERT_NE(kappa1, kappa_y);
}

TEST_F(TestTheoryWhitePbvIntblaster, computeKappa_int_to_pbv)
{
  Env& env = d_slvEngine->getEnv();
  PIntBlaster blaster(env);

  // INT_TO_PBV(k, val):  κ = k  (the first child, already Int)
  Node k   = mkInt(8);
  Node val = mkInt(42);
  Node t   = d_nodeManager->mkNode(Kind::INT_TO_PBV, k, val);
  Node kappa = blaster.computeKappa(t);
  ASSERT_EQ(kappa, k);
}

TEST_F(TestTheoryWhitePbvIntblaster, computeKappa_extract)
{
  Env& env = d_slvEngine->getEnv();
  PIntBlaster blaster(env);

  // PBV_EXTRACT(t, i, j): κ = i - j + 1
  Node x = mkPbvVar("x");
  Node i = mkInt(7);
  Node j = mkInt(3);
  Node extract = d_nodeManager->mkNode(Kind::PBV_EXTRACT, x, i, j);
  Node kappa   = blaster.computeKappa(extract);
  // Should be ADD(SUB(7,3), 1) = 5  (but symbolic, not evaluated)
  ASSERT_TRUE(kappa.getType().isInteger());
  // The expression must have kind ADD at the top
  ASSERT_EQ(kappa.getKind(), Kind::ADD);
}

TEST_F(TestTheoryWhitePbvIntblaster, computeKappa_concat)
{
  Env& env = d_slvEngine->getEnv();
  PIntBlaster blaster(env);

  // PBV_CONCAT(x, y): κ = κ(x) + κ(y)
  Node x    = mkPbvVar("x");
  Node y    = mkPbvVar("y");
  Node cat  = d_nodeManager->mkNode(Kind::PBV_CONCAT, x, y);
  Node kappa = blaster.computeKappa(cat);
  ASSERT_EQ(kappa.getKind(), Kind::ADD);
  // The two addends should be the kappas of x and y
  Node kx = blaster.computeKappa(x);
  Node ky = blaster.computeKappa(y);
  ASSERT_EQ(kappa[0], kx);
  ASSERT_EQ(kappa[1], ky);
}

TEST_F(TestTheoryWhitePbvIntblaster, computeKappa_zero_extend)
{
  Env& env = d_slvEngine->getEnv();
  PIntBlaster blaster(env);

  // PBV_ZERO_EXTEND(n, x): κ = κ(x) + n
  Node x   = mkPbvVar("x");
  Node n   = mkInt(4);
  Node ext = d_nodeManager->mkNode(Kind::PBV_ZERO_EXTEND, n, x);
  Node kappa = blaster.computeKappa(ext);
  ASSERT_EQ(kappa.getKind(), Kind::ADD);
  ASSERT_EQ(kappa[0], blaster.computeKappa(x));
  ASSERT_EQ(kappa[1], n);
}

// ============================================================================
// 3. translateWithChildren — Algorithm 3 operator cases
// ============================================================================

class TestTheoryWhitePbvIntblasterOps : public TestTheoryWhitePbvIntblaster
{
 protected:
  void SetUp() override
  {
    TestTheoryWhitePbvIntblaster::SetUp();
    // Create two PBV variables and their translated integer counterparts
    v1 = mkPbvVar("v1");
    v2 = mkPbvVar("v2");
    std::vector<TrustNode> lem;
    std::map<Node, Node> sk;
    PIntBlaster tmp(d_slvEngine->getEnv());
    i1 = tmp.translateNoChildren(v1, lem, sk);
    i2 = tmp.translateNoChildren(v2, lem, sk);
  }

  Node v1, v2;   // original PBV vars
  Node i1, i2;   // χ(v1), χ(v2)
};

TEST_F(TestTheoryWhitePbvIntblasterOps, translate_arithmetic)
{
  Env& env = d_slvEngine->getEnv();
  std::vector<TrustNode> lemmas;
  std::map<Node, Node>   skolems;
  PIntBlaster blaster(env);
  // Re-register v1/v2 with this blaster so κ(v1) is known
  blaster.translateNoChildren(v1, lemmas, skolems);
  blaster.translateNoChildren(v2, lemmas, skolems);

  Node result;

  // PBV_ADD → Int (with mod pow2)
  Node add = d_nodeManager->mkNode(Kind::PBV_ADD, v1, v2);
  result   = blaster.translateWithChildren(add, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());

  // PBV_SUB → Int
  Node sub = d_nodeManager->mkNode(Kind::PBV_SUB, v1, v2);
  result   = blaster.translateWithChildren(sub, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());

  // PBV_MULT → Int
  Node mul = d_nodeManager->mkNode(Kind::PBV_MULT, v1, v2);
  result   = blaster.translateWithChildren(mul, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());

  // PBV_NEG → Int (mod pow2)
  Node neg = d_nodeManager->mkNode(Kind::PBV_NEG, v1);
  result   = blaster.translateWithChildren(neg, {i1}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());

  // PBV_UDIV → Int (ITE node)
  Node udiv = d_nodeManager->mkNode(Kind::PBV_UDIV, v1, v2);
  result    = blaster.translateWithChildren(udiv, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());
  ASSERT_EQ(result.getKind(), Kind::ITE);

  // PBV_UREM → Int (ITE node)
  Node urem = d_nodeManager->mkNode(Kind::PBV_UREM, v1, v2);
  result    = blaster.translateWithChildren(urem, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());
  ASSERT_EQ(result.getKind(), Kind::ITE);
}

TEST_F(TestTheoryWhitePbvIntblasterOps, translate_bitwise)
{
  Env& env = d_slvEngine->getEnv();
  std::vector<TrustNode> lemmas;
  std::map<Node, Node>   skolems;
  PIntBlaster blaster(env);
  blaster.translateNoChildren(v1, lemmas, skolems);
  blaster.translateNoChildren(v2, lemmas, skolems);

  Node result;

  // PBV_NOT → Int (pow2(k) - (x+1))
  Node pbvnot = d_nodeManager->mkNode(Kind::PBV_NOT, v1);
  result      = blaster.translateWithChildren(pbvnot, {i1}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());
  ASSERT_EQ(result.getKind(), Kind::SUB);

  // PBV_AND → PIAND
  Node pbvand = d_nodeManager->mkNode(Kind::PBV_AND, v1, v2);
  result      = blaster.translateWithChildren(pbvand, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());
  ASSERT_EQ(result.getKind(), Kind::PIAND);

  // PBV_OR → SUB(ADD(i1,i2), piand)
  Node pbvor = d_nodeManager->mkNode(Kind::PBV_OR, v1, v2);
  result     = blaster.translateWithChildren(pbvor, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());
  ASSERT_EQ(result.getKind(), Kind::SUB);

  // PBV_XOR → SUB(ADD(i1,i2), 2*piand)
  Node pbvxor = d_nodeManager->mkNode(Kind::PBV_XOR, v1, v2);
  result      = blaster.translateWithChildren(pbvxor, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());
  ASSERT_EQ(result.getKind(), Kind::SUB);
}

TEST_F(TestTheoryWhitePbvIntblasterOps, translate_shifts)
{
  Env& env = d_slvEngine->getEnv();
  std::vector<TrustNode> lemmas;
  std::map<Node, Node>   skolems;
  PIntBlaster blaster(env);
  blaster.translateNoChildren(v1, lemmas, skolems);
  blaster.translateNoChildren(v2, lemmas, skolems);

  Node result;

  // PBV_SHL → INTS_MODULUS_TOTAL (after multiply by pow2)
  Node shl = d_nodeManager->mkNode(Kind::PBV_SHL, v1, v2);
  result   = blaster.translateWithChildren(shl, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());

  // PBV_LSHR → INTS_DIVISION_TOTAL
  Node lshr = d_nodeManager->mkNode(Kind::PBV_LSHR, v1, v2);
  result    = blaster.translateWithChildren(lshr, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());
  ASSERT_EQ(result.getKind(), Kind::INTS_DIVISION_TOTAL);

  // PBV_ASHR → ITE
  Node ashr = d_nodeManager->mkNode(Kind::PBV_ASHR, v1, v2);
  result    = blaster.translateWithChildren(ashr, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());
  ASSERT_EQ(result.getKind(), Kind::ITE);
}

TEST_F(TestTheoryWhitePbvIntblasterOps, translate_comparisons)
{
  Env& env = d_slvEngine->getEnv();
  std::vector<TrustNode> lemmas;
  std::map<Node, Node>   skolems;
  PIntBlaster blaster(env);
  blaster.translateNoChildren(v1, lemmas, skolems);
  blaster.translateNoChildren(v2, lemmas, skolems);

  Node result;

  // EQUAL on PBV → Bool
  Node eq = d_nodeManager->mkNode(Kind::EQUAL, v1, v2);
  result  = blaster.translateWithChildren(eq, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isBoolean());
  ASSERT_EQ(result.getKind(), Kind::EQUAL);

  // PBV_ULT → LT (Bool)
  Node ult = d_nodeManager->mkNode(Kind::PBV_ULT, v1, v2);
  result   = blaster.translateWithChildren(ult, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isBoolean());
  ASSERT_EQ(result.getKind(), Kind::LT);

  // PBV_ULE → LEQ
  Node ule = d_nodeManager->mkNode(Kind::PBV_ULE, v1, v2);
  result   = blaster.translateWithChildren(ule, {i1, i2}, lemmas);
  ASSERT_EQ(result.getKind(), Kind::LEQ);

  // PBV_UGT → GT
  Node ugt = d_nodeManager->mkNode(Kind::PBV_UGT, v1, v2);
  result   = blaster.translateWithChildren(ugt, {i1, i2}, lemmas);
  ASSERT_EQ(result.getKind(), Kind::GT);

  // PBV_UGE → GEQ
  Node uge = d_nodeManager->mkNode(Kind::PBV_UGE, v1, v2);
  result   = blaster.translateWithChildren(uge, {i1, i2}, lemmas);
  ASSERT_EQ(result.getKind(), Kind::GEQ);

  // PBV_SLT → LT (Bool, using utsSym conversion)
  Node slt = d_nodeManager->mkNode(Kind::PBV_SLT, v1, v2);
  result   = blaster.translateWithChildren(slt, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isBoolean());
  ASSERT_EQ(result.getKind(), Kind::LT);

  // PBV_SLE, SGT, SGE
  Node sle = d_nodeManager->mkNode(Kind::PBV_SLE, v1, v2);
  result   = blaster.translateWithChildren(sle, {i1, i2}, lemmas);
  ASSERT_EQ(result.getKind(), Kind::LEQ);

  Node sgt = d_nodeManager->mkNode(Kind::PBV_SGT, v1, v2);
  result   = blaster.translateWithChildren(sgt, {i1, i2}, lemmas);
  ASSERT_EQ(result.getKind(), Kind::GT);

  Node sge = d_nodeManager->mkNode(Kind::PBV_SGE, v1, v2);
  result   = blaster.translateWithChildren(sge, {i1, i2}, lemmas);
  ASSERT_EQ(result.getKind(), Kind::GEQ);
}

TEST_F(TestTheoryWhitePbvIntblasterOps, translate_structural)
{
  Env& env = d_slvEngine->getEnv();
  std::vector<TrustNode> lemmas;
  std::map<Node, Node>   skolems;
  PIntBlaster blaster(env);
  blaster.translateNoChildren(v1, lemmas, skolems);
  blaster.translateNoChildren(v2, lemmas, skolems);

  Node result;
  Node n = mkInt(4);
  Node k = mkInt(8);

  // PBV_CONCAT → ADD(MULT(i1, pow2(κ(v2))), i2)
  Node cat = d_nodeManager->mkNode(Kind::PBV_CONCAT, v1, v2);
  result   = blaster.translateWithChildren(cat, {i1, i2}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());
  ASSERT_EQ(result.getKind(), Kind::ADD);

  // PBV_EXTRACT(v1, 7, 3): κ = 5
  Node i7 = mkInt(7);
  Node i3 = mkInt(3);
  Node extract = d_nodeManager->mkNode(Kind::PBV_EXTRACT, v1, i7, i3);
  result       = blaster.translateWithChildren(extract, {i1, i7, i3}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());

  // PBV_ZERO_EXTEND(4, v1) → i1 (unchanged value)
  Node zext = d_nodeManager->mkNode(Kind::PBV_ZERO_EXTEND, n, v1);
  result    = blaster.translateWithChildren(zext, {n, i1}, lemmas);
  ASSERT_EQ(result, i1);

  // PBV_SIGN_EXTEND(4, v1) → ITE
  Node sext = d_nodeManager->mkNode(Kind::PBV_SIGN_EXTEND, n, v1);
  result    = blaster.translateWithChildren(sext, {n, i1}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());
  ASSERT_EQ(result.getKind(), Kind::ITE);

  // INT_TO_PBV(k, val) → val mod pow2(k)
  Node val      = mkInt(42);
  Node intToPbv = d_nodeManager->mkNode(Kind::INT_TO_PBV, k, val);
  result        = blaster.translateWithChildren(intToPbv, {k, val}, lemmas);
  ASSERT_TRUE(result.getType().isInteger());
  ASSERT_EQ(result.getKind(), Kind::INTS_MODULUS_TOTAL);

  // PBV_SIZE(v1) → κ(v1)
  Node sz    = d_nodeManager->mkNode(Kind::PBV_SIZE, v1);
  result     = blaster.translateWithChildren(sz, {i1}, lemmas);
  Node kappa = blaster.computeKappa(v1);
  ASSERT_EQ(result, kappa);
}

// ============================================================================
// 4. Range constraints  (RANGE function, Algorithm 4)
// ============================================================================

TEST_F(TestTheoryWhitePbvIntblaster, range_constraints_emitted)
{
  Env& env = d_slvEngine->getEnv();
  std::vector<TrustNode> lemmas;
  PIntBlaster blaster(env);

  // Build a simple formula: (PBV_ULT x y)
  Node x     = mkPbvVar("x");
  Node y     = mkPbvVar("y");
  Node fml   = d_nodeManager->mkNode(Kind::PBV_ULT, x, y);

  blaster.addRangeConstraints(fml, lemmas);

  // We should get one range lemma per variable (x and y), so at least 2
  ASSERT_GE(lemmas.size(), (size_t)2);

  // Each lemma should be a conjunction of two inequalities (AND)
  for (const TrustNode& tlem : lemmas)
  {
    Node lem = tlem.getProven();
    ASSERT_EQ(lem.getKind(), Kind::AND);
    ASSERT_EQ(lem.getNumChildren(), 2u);
    // Lower bound: 0 <= chi
    ASSERT_EQ(lem[0].getKind(), Kind::LEQ);
    // Upper bound: chi < pow2(kappa)
    ASSERT_EQ(lem[1].getKind(), Kind::LT);
    // Upper bound RHS should be POW2
    ASSERT_EQ(lem[1][1].getKind(), Kind::POW2);
  }
}

TEST_F(TestTheoryWhitePbvIntblaster, range_constraints_no_duplicates)
{
  Env& env = d_slvEngine->getEnv();
  std::vector<TrustNode> lemmas;
  PIntBlaster blaster(env);

  Node x   = mkPbvVar("x");
  Node fml = d_nodeManager->mkNode(Kind::PBV_ULT, x, x);  // x < x (unsat)

  blaster.addRangeConstraints(fml, lemmas);
  // Despite x appearing twice, only one range lemma should be emitted
  ASSERT_EQ(lemmas.size(), (size_t)1);
}

// ============================================================================
// 5. Admissibility constraints  (ADM function, Algorithm 1)
// ============================================================================

TEST_F(TestTheoryWhitePbvIntblaster, adm_constraints_width_positive)
{
  Env& env = d_slvEngine->getEnv();
  std::vector<TrustNode> lemmas;
  PIntBlaster blaster(env);

  Node x   = mkPbvVar("x");
  Node fml = d_nodeManager->mkNode(Kind::PBV_NOT, x);

  blaster.addAdmConstraints(fml, lemmas);

  // Must find a lemma of the form κ(x) > 0
  bool found = false;
  for (const TrustNode& tlem : lemmas)
  {
    Node lem = tlem.getProven();
    if (lem.getKind() == Kind::GT && lem[1].isConst()
        && lem[1].getConst<Rational>() == Rational(0))
    {
      found = true;
      break;
    }
  }
  ASSERT_TRUE(found) << "Expected κ(x) > 0 admissibility lemma not found";
}

TEST_F(TestTheoryWhitePbvIntblaster, adm_constraints_equal_width)
{
  Env& env = d_slvEngine->getEnv();
  std::vector<TrustNode> lemmas;
  PIntBlaster blaster(env);

  // (PBV_ADD x y): must emit κ(x) = κ(y)
  Node x   = mkPbvVar("x");
  Node y   = mkPbvVar("y");
  Node fml = d_nodeManager->mkNode(Kind::PBV_ADD, x, y);

  blaster.addAdmConstraints(fml, lemmas);

  Node kx = blaster.computeKappa(x);
  Node ky = blaster.computeKappa(y);

  bool foundWidthEq = false;
  for (const TrustNode& tlem : lemmas)
  {
    Node lem = tlem.getProven();
    if (lem.getKind() == Kind::EQUAL
        && ((lem[0] == kx && lem[1] == ky)
            || (lem[0] == ky && lem[1] == kx)))
    {
      foundWidthEq = true;
      break;
    }
  }
  ASSERT_TRUE(foundWidthEq) << "Expected κ(x) = κ(y) equal-width lemma";
}

// ============================================================================
// 6. End-to-end: trustedIntBlast
// ============================================================================

TEST_F(TestTheoryWhitePbvIntblaster, e2e_equal_pbv)
{
  Env& env = d_slvEngine->getEnv();
  std::vector<TrustNode> lemmas;
  std::map<Node, Node>   skolems;
  PIntBlaster blaster(env);

  // Formula: (= x y)  where x, y are PBV variables
  Node x   = mkPbvVar("x");
  Node y   = mkPbvVar("y");
  Node fml = d_nodeManager->mkNode(Kind::EQUAL, x, y);
  // rewrite it first (trustedIntBlast requires this)
  fml = d_slvEngine->getEnv().getRewriter()->rewrite(fml);

  TrustNode tr = blaster.trustedIntBlast(fml, lemmas, skolems);
  // Result should not be null (formula was changed)
  ASSERT_FALSE(tr.isNull());
  // The translation is an equality over integers
  Node result = tr.getNode();
  ASSERT_EQ(result.getKind(), Kind::EQUAL);
  ASSERT_TRUE(result[0].getType().isInteger());
  ASSERT_TRUE(result[1].getType().isInteger());
}

TEST_F(TestTheoryWhitePbvIntblaster, e2e_add_and_compare)
{
  Env& env = d_slvEngine->getEnv();
  std::vector<TrustNode> lemmas;
  std::map<Node, Node>   skolems;
  PIntBlaster blaster(env);

  // Formula: (PBV_ULT (PBV_ADD x y) x)
  Node x   = mkPbvVar("x");
  Node y   = mkPbvVar("y");
  Node sum = d_nodeManager->mkNode(Kind::PBV_ADD, x, y);
  Node fml = d_nodeManager->mkNode(Kind::PBV_ULT, sum, x);
  fml      = d_slvEngine->getEnv().getRewriter()->rewrite(fml);

  TrustNode tr = blaster.trustedIntBlast(fml, lemmas, skolems);
  ASSERT_FALSE(tr.isNull());
  Node result = tr.getNode();
  // Top-level should be LT (unsigned less-than → integer less-than)
  ASSERT_EQ(result.getKind(), Kind::LT);
  ASSERT_TRUE(result[0].getType().isInteger());

  // Should have emitted RANGE and ADM lemmas for x and y
  ASSERT_GE(lemmas.size(), (size_t)4);  // ≥2 range + ≥2 adm

  // Both x and y should have skolem entries
  ASSERT_TRUE(skolems.count(x) > 0);
  ASSERT_TRUE(skolems.count(y) > 0);
}

TEST_F(TestTheoryWhitePbvIntblaster, e2e_int_to_pbv_roundtrip)
{
  Env& env = d_slvEngine->getEnv();
  std::vector<TrustNode> lemmas;
  std::map<Node, Node>   skolems;
  PIntBlaster blaster(env);

  // Formula: (= (INT_TO_PBV 8 n) x)  where n is Int, x is PBV
  Node n    = mkIntVar("n");
  Node x    = mkPbvVar("x");
  Node k    = mkInt(8);
  Node cast = d_nodeManager->mkNode(Kind::INT_TO_PBV, k, n);
  Node fml  = d_nodeManager->mkNode(Kind::EQUAL, cast, x);
  fml       = d_slvEngine->getEnv().getRewriter()->rewrite(fml);

  TrustNode tr = blaster.trustedIntBlast(fml, lemmas, skolems);
  ASSERT_FALSE(tr.isNull());
  Node result = tr.getNode();
  // Should be: (= (n mod pow2(8)) chi_x)
  ASSERT_EQ(result.getKind(), Kind::EQUAL);
  // Left side should involve INTS_MODULUS_TOTAL
  bool hasModPow2 = (result[0].getKind() == Kind::INTS_MODULUS_TOTAL
                     || result[1].getKind() == Kind::INTS_MODULUS_TOTAL);
  ASSERT_TRUE(hasModPow2) << "Expected n mod pow2(k) in CONV(INT_TO_PBV(k,n))";
}

TEST_F(TestTheoryWhitePbvIntblaster, e2e_bitwise_and_uses_piand)
{
  Env& env = d_slvEngine->getEnv();
  std::vector<TrustNode> lemmas;
  std::map<Node, Node>   skolems;
  PIntBlaster blaster(env);

  // Formula: (= (PBV_AND x y) x)
  Node x    = mkPbvVar("x");
  Node y    = mkPbvVar("y");
  Node band = d_nodeManager->mkNode(Kind::PBV_AND, x, y);
  Node fml  = d_nodeManager->mkNode(Kind::EQUAL, band, x);
  fml       = d_slvEngine->getEnv().getRewriter()->rewrite(fml);

  TrustNode tr = blaster.trustedIntBlast(fml, lemmas, skolems);
  ASSERT_FALSE(tr.isNull());

  // The translation of PBV_AND must be a PIAND node somewhere in the result
  std::function<bool(Node)> hasPiand = [&](Node n) -> bool {
    if (n.getKind() == Kind::PIAND) return true;
    for (const Node& c : n) if (hasPiand(c)) return true;
    return false;
  };
  ASSERT_TRUE(hasPiand(tr.getNode()))
      << "Expected Kind::PIAND in translation of PBV_AND";
}

TEST_F(TestTheoryWhitePbvIntblaster, e2e_sign_extend)
{
  Env& env = d_slvEngine->getEnv();
  std::vector<TrustNode> lemmas;
  std::map<Node, Node>   skolems;
  PIntBlaster blaster(env);

  // Formula: (PBV_ULT (PBV_SIGN_EXTEND 4 x) y)
  Node x    = mkPbvVar("x");
  Node y    = mkPbvVar("y");
  Node n    = mkInt(4);
  Node sext = d_nodeManager->mkNode(Kind::PBV_SIGN_EXTEND, n, x);
  Node fml  = d_nodeManager->mkNode(Kind::PBV_ULT, sext, y);
  fml       = d_slvEngine->getEnv().getRewriter()->rewrite(fml);

  TrustNode tr = blaster.trustedIntBlast(fml, lemmas, skolems);
  ASSERT_FALSE(tr.isNull());
  // Sign-extend must produce an ITE node
  Node result = tr.getNode();
  ASSERT_EQ(result.getKind(), Kind::LT);  // outer ULT → LT
  // Left child of LT should be the sign-extend ITE
  ASSERT_EQ(result[0].getKind(), Kind::ITE);
}

}  // namespace test
}  // namespace cvc5::internal
