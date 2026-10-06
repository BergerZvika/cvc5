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
 * Implementation of the arith-fermat-vacuity preprocessing pass.
 */

#include "preprocessing/passes/arith_fermat_vacuity.h"

#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node_algorithm.h"
#include "options/arith_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/arith/arith_msum.h"
#include "theory/rewriter.h"
#include "util/integer.h"
#include "util/statistics_registry.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace cvc5::internal::theory;

namespace {

/**
 * A monomial of the reduced form: variable (or opaque atom) -> exponent, with
 * every exponent already collapsed into [1, p-1]. Absent means exponent 0.
 */
using Mono = std::map<Node, uint32_t>;
/** A reduced polynomial over F_p: monomial -> coefficient in [1, p-1]. */
using Poly = std::map<Mono, uint32_t>;

/**
 * Cap on the number of monomials in any intermediate polynomial. This guards
 * expansion of a nested product such as (x+y+z)^6; it is NOT a bound on the
 * number of variables, which the method does not care about.
 */
const size_t s_monoBudget = 200000;

/**
 * Collapse an exponent to its representative in [1, p-1], which is the whole
 * of Fermat's little theorem: for x in F_p, x^e as a FUNCTION depends only on
 * whether e is 0 and, when e >= 1, on e mod (p-1). (For x != 0 that is
 * x^(p-1) = 1; for x = 0 both sides are 0 as long as the representative stays
 * >= 1, which is why the residue is taken of e-1 and shifted back up.)
 */
uint32_t redExp(uint32_t e, uint32_t p)
{
  if (e == 0)
  {
    return 0;
  }
  if (p == 2)
  {
    return 1;
  }
  return ((e - 1) % (p - 1)) + 1;
}

/** poly += c * mo, in F_p. */
void addTerm(Poly& poly, const Mono& mo, uint32_t c, uint32_t p)
{
  c %= p;
  if (c == 0)
  {
    return;
  }
  Poly::iterator it = poly.find(mo);
  if (it == poly.end())
  {
    poly[mo] = c;
    return;
  }
  uint32_t nv = (it->second + c) % p;
  if (nv == 0)
  {
    // the cancellation that makes the whole method work
    poly.erase(it);
  }
  else
  {
    it->second = nv;
  }
}

/** out = a * b in F_p[x]/(x^p - x). False if the monomial budget is blown. */
bool polyMul(const Poly& a, const Poly& b, Poly& out, uint32_t p)
{
  out.clear();
  for (const std::pair<const Mono, uint32_t>& ma : a)
  {
    for (const std::pair<const Mono, uint32_t>& mb : b)
    {
      Mono mo = ma.first;
      for (const std::pair<const Node, uint32_t>& ve : mb.first)
      {
        uint32_t& e = mo[ve.first];
        // reduction is a homomorphism, so it may be applied at every step
        // rather than only at the end
        e = redExp(e + ve.second, p);
      }
      addTerm(out, mo, uint32_t((uint64_t(ma.second) * mb.second) % p), p);
      if (out.size() > s_monoBudget)
      {
        return false;
      }
    }
  }
  return true;
}

/**
 * Build the reduced form of `n` over F_p. Returns false if `n` cannot be read
 * as an integer polynomial at all, or if the budget is exceeded.
 *
 * Any integer subterm that is not built from +, -, *, and constant powers is
 * kept as an OPAQUE ATOM and treated as one more variable. Two syntactically
 * equal atoms are the same variable; distinct ones are independent. This can
 * only weaken the conclusion, since certifying that Q vanishes for all values
 * of the atom certifies it for the value the atom actually takes.
 */
bool buildPoly(TNode n, uint32_t p, Poly& out)
{
  out.clear();
  if (n.isConst())
  {
    Kind ck = n.getKind();
    if (ck != Kind::CONST_INTEGER && ck != Kind::CONST_RATIONAL)
    {
      return false;
    }
    const Rational& r = n.getConst<Rational>();
    if (!r.isIntegral())
    {
      return false;
    }
    // euclidian remainder is non-negative, which is what F_p wants
    Integer rem =
        r.getNumerator().euclidianDivideRemainder(Integer(uint32_t(p)));
    addTerm(out, Mono(), uint32_t(rem.toUnsignedInt()), p);
    return true;
  }

  Kind k = n.getKind();
  switch (k)
  {
    case Kind::ADD:
    {
      for (const Node& c : n)
      {
        Poly pc;
        if (!buildPoly(c, p, pc))
        {
          return false;
        }
        for (const std::pair<const Mono, uint32_t>& t : pc)
        {
          addTerm(out, t.first, t.second, p);
        }
        if (out.size() > s_monoBudget)
        {
          return false;
        }
      }
      return true;
    }
    case Kind::SUB:
    {
      Poly pa, pb;
      if (!buildPoly(n[0], p, pa) || !buildPoly(n[1], p, pb))
      {
        return false;
      }
      out = pa;
      for (const std::pair<const Mono, uint32_t>& t : pb)
      {
        addTerm(out, t.first, p - t.second, p);
      }
      return true;
    }
    case Kind::NEG:
    {
      Poly pa;
      if (!buildPoly(n[0], p, pa))
      {
        return false;
      }
      for (const std::pair<const Mono, uint32_t>& t : pa)
      {
        addTerm(out, t.first, p - t.second, p);
      }
      return true;
    }
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
    {
      Poly acc;
      addTerm(acc, Mono(), 1, p);
      for (const Node& c : n)
      {
        Poly pc, prod;
        if (!buildPoly(c, p, pc) || !polyMul(acc, pc, prod, p))
        {
          return false;
        }
        acc = prod;
      }
      out = acc;
      return true;
    }
    case Kind::POW:
    case Kind::EXP:
    {
      // Only a constant, non-negative exponent is polynomial. EXP with a
      // negative exponent is `1 div s^|t|` under this solver's '**', and with
      // a symbolic exponent it is not a polynomial either -- both fall through
      // to the opaque-atom case below.
      if (!n[1].isConst())
      {
        break;
      }
      const Rational& re = n[1].getConst<Rational>();
      if (!re.isIntegral() || re.sgn() < 0)
      {
        break;
      }
      Integer ei = re.getNumerator();
      if (!ei.fitsUnsignedInt() || ei > Integer(64))
      {
        break;
      }
      uint32_t e = ei.toUnsignedInt();
      Poly base;
      if (!buildPoly(n[0], p, base))
      {
        return false;
      }
      Poly acc;
      addTerm(acc, Mono(), 1, p);
      for (uint32_t j = 0; j < e; ++j)
      {
        Poly prod;
        if (!polyMul(acc, base, prod, p))
        {
          return false;
        }
        acc = prod;
      }
      out = acc;
      return true;
    }
    default: break;
  }

  // variable, or opaque integer atom
  if (!n.getType().isInteger())
  {
    return false;
  }
  Mono mo;
  mo[Node(n)] = redExp(1, p);
  addTerm(out, mo, 1, p);
  return true;
}

/**
 * Squarefree prime factorisation of m >= 2. False if m is not squarefree, in
 * which case the CRT argument used here does not apply and the caller
 * declines.
 */
bool squarefreePrimes(uint32_t m, std::vector<uint32_t>& ps)
{
  for (uint32_t d = 2; uint64_t(d) * d <= m; ++d)
  {
    if (m % d != 0)
    {
      continue;
    }
    m /= d;
    if (m % d == 0)
    {
      return false;
    }
    ps.push_back(d);
  }
  if (m > 1)
  {
    ps.push_back(m);
  }
  return !ps.empty();
}

/** Free integer variables of n, accumulated into vs. */
void collectVars(TNode n,
                 std::unordered_set<Node>& vs,
                 std::unordered_set<TNode>& visited)
{
  if (!visited.insert(n).second)
  {
    return;
  }
  if (n.isVar() && n.getKind() != Kind::BOUND_VARIABLE
      && n.getType().isInteger())
  {
    vs.insert(n);
    return;
  }
  for (const Node& c : n)
  {
    collectVars(c, vs, visited);
  }
}

/**
 * Does n contain an INTS_MODULUS (or its total variant) whose MODULUS -- the
 * second operand -- contains an EXP or POW term, e.g. `(mod t (exp 2 k))`?
 * This is the shape --arith-fermat-vacuity-skip-mod-exp declines. An `exp`
 * in the dividend only, `(mod (exp 2 k) m)`, does not count.
 */
bool hasExpAsModulus(TNode n)
{
  std::unordered_set<Node> mods;
  expr::getKindSubterms(n, Kind::INTS_MODULUS, false, mods);
  expr::getKindSubterms(n, Kind::INTS_MODULUS_TOTAL, false, mods);
  for (const Node& m : mods)
  {
    if (expr::hasSubtermKind(Kind::EXP, m[1])
        || expr::hasSubtermKind(Kind::POW, m[1]))
    {
      return true;
    }
  }
  return false;
}

}  // namespace

ArithFermatVacuity::ArithFermatVacuity(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "arith-fermat-vacuity"),
      d_stats(statisticsRegistry())
{
}

ArithFermatVacuity::Statistics::Statistics(StatisticsRegistry& reg)
    : d_numVacuous(reg.registerInt(
        "preprocessing::passes::ArithFermatVacuity::NumVacuous")),
      d_numDeclined(reg.registerInt(
          "preprocessing::passes::ArithFermatVacuity::NumDeclined"))
{
}

bool ArithFermatVacuity::certifyVanishes(TNode q, const Integer& m)
{
  Assert(m >= Integer(2));
  if (!m.fitsUnsignedInt())
  {
    return false;
  }
  std::vector<uint32_t> ps;
  if (!squarefreePrimes(m.toUnsignedInt(), ps))
  {
    return false;
  }
  // m | Q identically iff p | Q identically for every prime p | m (CRT), which
  // needs the factorisation to be squarefree -- guaranteed above.
  uint64_t maxPrime = options().arith.arithFermatVacuityMaxPrime;
  for (uint32_t p : ps)
  {
    // Optional cap on the prime: over a large F_p nothing collapses and the
    // normal form is just the expanded polynomial, so the user may decline.
    if (maxPrime > 0 && uint64_t(p) > maxPrime)
    {
      Trace("arith-fermat-vacuity")
          << "declined (prime " << p << " > " << maxPrime << ")" << std::endl;
      return false;
    }
    Poly poly;
    if (!buildPoly(q, p, poly))
    {
      return false;
    }
    if (!poly.empty())
    {
      // the reduced form is a normal form, so a non-empty one is a genuine
      // witness that Q does not vanish identically mod p
      return false;
    }
  }
  return true;
}

bool ArithFermatVacuity::sweep(AssertionPipeline* ap)
{
  NodeManager* nm = nodeManager();
  // Number of ASSERTIONS mentioning each integer variable. A candidate needs a
  // total of 1; that it occurs exactly once WITHIN that assertion is checked
  // below against the monomial sum, which is cheaper than a DAG-aware count.
  std::unordered_map<Node, size_t> count;
  for (size_t i = 0, n = ap->size(); i < n; ++i)
  {
    std::unordered_set<Node> vs;
    std::unordered_set<TNode> visited;
    collectVars((*ap)[i], vs, visited);
    for (const Node& v : vs)
    {
      count[v] += 1;
    }
  }

  bool changed = false;
  for (size_t i = 0, nasserts = ap->size(); i < nasserts; ++i)
  {
    Node a = (*ap)[i];
    if (a.getKind() != Kind::EQUAL || !a[0].getType().isInteger()
        || expr::hasBoundVar(a))
    {
      continue;
    }
    std::map<Node, Node> msum;
    if (!ArithMSum::getMonomialSumLit(a, msum))
    {
      continue;
    }
    for (const std::pair<const Node, Node>& m : msum)
    {
      Node v = m.first;
      // the constant term has a null monomial
      if (v.isNull() || !v.isVar() || !v.getType().isInteger())
      {
        continue;
      }
      std::unordered_map<Node, size_t>::const_iterator it = count.find(v);
      if (it == count.end() || it->second != 1)
      {
        continue;
      }
      // v must occur ONLY as this monomial: if it also sits inside another
      // monomial of the same equality it is not free to absorb the rest.
      bool elsewhere = false;
      for (const std::pair<const Node, Node>& o : msum)
      {
        if (o.first == v || o.first.isNull())
        {
          continue;
        }
        if (expr::hasSubterm(o.first, v))
        {
          elsewhere = true;
          break;
        }
      }
      if (elsewhere)
      {
        continue;
      }
      Rational c =
          m.second.isNull() ? Rational(1) : m.second.getConst<Rational>();
      if (!c.isIntegral() || c.sgn() == 0)
      {
        continue;
      }
      Integer ac = c.getNumerator().abs();
      // rest = [msum] with v's monomial removed, i.e. the Q of c*v + Q = 0
      std::map<Node, Node> rest = msum;
      rest.erase(v);
      Node q = ArithMSum::mkNode(nm, rest);
      // Optionally refuse to touch an equality with an exponential as the
      // MODULUS of a mod: the opaque-atom treatment would be sound, but the
      // user has asked for those equalities to be left exactly as written.
      if (options().arith.arithFermatVacuitySkipModExp && hasExpAsModulus(q))
      {
        Trace("arith-fermat-vacuity")
            << "declined (exp as modulus): " << a << std::endl;
        ++d_stats.d_numDeclined;
        continue;
      }
      if (ac > Integer(1) && !certifyVanishes(q, ac))
      {
        // not certified vacuous; leave the assertion exactly as it was
        ++d_stats.d_numDeclined;
        continue;
      }
      // c*v + Q = 0 is solvable for v at every assignment, and v is
      // constrained nowhere else, so the assertion says nothing. Record the
      // witness so the model still satisfies the ORIGINAL equality: the
      // division is exact, which is precisely what was just certified.
      Node witness = rewrite(nm->mkNode(Kind::INTS_DIVISION_TOTAL,
                                        nm->mkNode(Kind::NEG, q),
                                        nm->mkConstInt(c)));
      d_preprocContext->addSubstitution(v, witness);
      Trace("arith-fermat-vacuity")
          << "vacuous: " << a << "\n  singleton " << v << " coeff " << c
          << "\n  witness " << witness << std::endl;
      ap->replace(i, nm->mkConst(true));
      ++d_stats.d_numVacuous;
      changed = true;
      break;
    }
  }
  return changed;
}

PreprocessingPassResult ArithFermatVacuity::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  // Deleting an assertion can make a further variable a singleton, so the
  // sweep is iterated to a fixpoint. The `size0*` shapes close after two.
  for (uint32_t round = 0; round < 8; ++round)
  {
    if (!sweep(assertionsToPreprocess))
    {
      break;
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
