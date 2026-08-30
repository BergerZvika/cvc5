#!/usr/bin/env python3
###############################################################################
# generate_rewriter.py
#
# Parses src/theory/pbv/rewrites (RARE DSL) and emits two C++ files:
#
#   theory_pbv_rewriter.h   – stable class header (TheoryPbvRewriter)
#   theory_pbv_rewriter.cpp – auto-generated implementation (RW_B, Appendix A)
#
# from: "Bit-Precise Reasoning with Parametric Bit-Vectors"
#       Berger, Zohar, Niemetz, Preiner, Reynolds, Barrett, Tinelli (SAT 2025)
#
# Usage (from the cvc5 source root):
#   python3 src/theory/pbv/generate_rewriter.py
#   python3 src/theory/pbv/generate_rewriter.py --output-dir /path/to/build/src/theory
###############################################################################

import argparse
import sys
from pathlib import Path
from collections import defaultdict

# ---------------------------------------------------------------------------
# Bootstrap sys.path for cvc5's RARE parser modules
# ---------------------------------------------------------------------------
SCRIPT_DIR   = Path(__file__).resolve().parent
CVC5_SRC     = SCRIPT_DIR.parent.parent
REWRITER_DIR = CVC5_SRC / "rewriter"

if str(REWRITER_DIR) not in sys.path:
    sys.path.insert(0, str(REWRITER_DIR))

try:
    from rw_parser import Parser
    from node import (Op, Node, Sort, BaseSort, Var, CBool, CInt, CRational,
                      CString, App, Placeholder)
    from rule import Rule
except ImportError as exc:
    sys.exit(
        f"ERROR: Cannot import cvc5 rewriter modules from {REWRITER_DIR}.\n"
        f"Underlying error: {exc}"
    )

REWRITES_FILE = SCRIPT_DIR / "rewrites"

###############################################################################
# LHS structural walker
#
# Walks the LHS pattern tree and produces:
#   var_ctx  : {Var -> first_accessor}   – C++ TNode accessor for each RARE var
#   guards   : list of C++ bool strings  – conditions that must hold at runtime
#
# Handles:
#   - Structural kind checks for nested Apps
#   - Duplicate Var occurrences (self-identity patterns like (pbvult x x))
#   - Literal constant patterns (CInt)
###############################################################################

def walk_lhs(pattern, accessor: str, var_ctx: dict, guards: list):
    if isinstance(pattern, Var):
        if pattern in var_ctx:
            # Same variable appears a second time in the LHS pattern:
            # emit a structural equality guard.
            guards.append(f"({var_ctx[pattern]} == {accessor})")
        else:
            var_ctx[pattern] = accessor
        return

    if isinstance(pattern, CInt):
        guards.append(
            f"({accessor}.isConst() && "
            f"{accessor}.getConst<Rational>() == Rational({pattern.val}))")
        return

    if isinstance(pattern, (CBool, CRational, CString)):
        # For completeness – not expected in PBV rules
        guards.append(f"({accessor} /* literal-guard */ )")
        return

    if isinstance(pattern, App):
        if accessor != "node":
            guards.append(f"({accessor}.getKind() == Kind::{pattern.op.kind})")
        for idx, child in enumerate(pattern.children):
            walk_lhs(child, f"{accessor}[{idx}]", var_ctx, guards)
        return

    if isinstance(pattern, Placeholder):
        return  # wildcard – match anything

    raise NotImplementedError(
        f"walk_lhs: unhandled pattern {type(pattern).__name__}")


###############################################################################
# RHS / condition Node -> C++ string
###############################################################################

def node_to_cpp(expr, var_ctx: dict) -> str:
    if isinstance(expr, Var):
        if expr in var_ctx:
            return var_ctx[expr]
        return expr.name  # fallback (should not happen)

    if isinstance(expr, CBool):
        return "nm->mkConst(true)" if expr.val else "nm->mkConst(false)"

    if isinstance(expr, CInt):
        return f"nm->mkConstInt(Rational({expr.val}))"

    if isinstance(expr, CRational):
        return f'nm->mkConstReal(internal::Rational("{expr.val}"))'

    if isinstance(expr, CString):
        return f'nm->mkConst(String("{expr.val}"))'

    if isinstance(expr, App):
        if expr.op == Op.NOT:
            return f"nm->mkNode(Kind::NOT, {{ {node_to_cpp(expr.children[0], var_ctx)} }})"
        if expr.op == Op.AND:
            args = ", ".join(node_to_cpp(c, var_ctx) for c in expr.children)
            return f"nm->mkNode(Kind::AND, {{ {args} }})"
        if expr.op == Op.OR:
            args = ", ".join(node_to_cpp(c, var_ctx) for c in expr.children)
            return f"nm->mkNode(Kind::OR, {{ {args} }})"
        if expr.op == Op.EQ:
            args = ", ".join(node_to_cpp(c, var_ctx) for c in expr.children)
            return f"nm->mkNode(Kind::EQUAL, {{ {args} }})"
        args = ", ".join(node_to_cpp(c, var_ctx) for c in expr.children)
        return f"nm->mkNode(Kind::{expr.op.kind}, {{ {args} }})"

    raise NotImplementedError(
        f"node_to_cpp: unhandled {type(expr).__name__}: {expr!r}")


###############################################################################
# Semantic side-condition -> C++ boolean string
#
# For the rules in Appendix A the conditions only involve:
#   (= IntVar ArithExpr)  and  (and ...)  and  (>= / <= / > / <)
# where ArithExpr uses +, -, pbvsize.
###############################################################################

def cond_to_cpp(cond, var_ctx: dict) -> str:
    """Return a C++ boolean string, or '' for CBool(True) (unconditional)."""
    if isinstance(cond, CBool):
        return "" if cond.val else "false"

    if isinstance(cond, App):
        if cond.op == Op.AND:
            parts = [cond_to_cpp(c, var_ctx) for c in cond.children]
            parts = [p for p in parts if p]
            return " && ".join(f"({p})" for p in parts) if parts else ""

        if cond.op in (Op.EQ, Op.GEQ, Op.LEQ, Op.GT, Op.LT):
            op_map = {Op.EQ: "==", Op.GEQ: ">=", Op.LEQ: "<=",
                      Op.GT: ">",  Op.LT:  "<"}
            lhs = arith_to_cpp(cond.children[0], var_ctx)
            rhs = arith_to_cpp(cond.children[1], var_ctx)
            return f"{lhs} {op_map[cond.op]} {rhs}"

        if cond.op == Op.NOT:
            return f"!({cond_to_cpp(cond.children[0], var_ctx)})"

    raise NotImplementedError(
        f"cond_to_cpp: unhandled {type(cond).__name__}: {cond!r}")


def _is_node_expr(expr, var_ctx: dict) -> bool:
    """
    Return True when the expression involves a Var bound to a TNode accessor
    (i.e. it will be represented as a Node in C++, not as a plain integer).
    """
    if isinstance(expr, Var):
        return expr in var_ctx
    if isinstance(expr, App):
        return any(_is_node_expr(c, var_ctx) for c in expr.children)
    return False


def arith_to_cpp(expr, var_ctx: dict) -> str:
    """
    Convert an integer arithmetic sub-expression to a C++ string.

    If *all* leaves are plain CInt literals the result is a plain C++ integer
    expression.  As soon as any leaf is a Var bound to a TNode accessor the
    entire expression is lifted to Node arithmetic so that the comparison
    operator in cond_to_cpp can emit a Node == Node check.
    """
    if isinstance(expr, CInt):
        return str(expr.val)

    if isinstance(expr, Var):
        if expr in var_ctx:
            return var_ctx[expr]   # TNode accessor, e.g. node[1][1]
        return expr.name

    if isinstance(expr, App):
        if expr.op == Op.ADD:
            # If any child involves a TNode, build a Node-level addition
            if _is_node_expr(expr, var_ctx):
                args = []
                for c in expr.children:
                    a = arith_to_cpp(c, var_ctx)
                    if isinstance(c, CInt):
                        a = f"nm->mkConstInt(Rational({c.val}))"
                    args.append(a)
                inner = ", ".join(args)
                return f"nm->mkNode(Kind::ADD, {{ {inner} }})"
            return "(" + " + ".join(arith_to_cpp(c, var_ctx) for c in expr.children) + ")"
        if expr.op == Op.SUB:
            if len(expr.children) == 1:
                inner = arith_to_cpp(expr.children[0], var_ctx)
                if _is_node_expr(expr.children[0], var_ctx):
                    return f"nm->mkNode(Kind::NEG, {{ {inner} }})"
                return f"(-{inner})"
            lhs = arith_to_cpp(expr.children[0], var_ctx)
            rhs = arith_to_cpp(expr.children[1], var_ctx)
            if _is_node_expr(expr, var_ctx):
                if isinstance(expr.children[0], CInt):
                    lhs = f"nm->mkConstInt(Rational({expr.children[0].val}))"
                if isinstance(expr.children[1], CInt):
                    rhs = f"nm->mkConstInt(Rational({expr.children[1].val}))"
                return f"nm->mkNode(Kind::SUB, {{ {lhs}, {rhs} }})"
            return f"({lhs} - {rhs})"
        if expr.op == Op.MULT:
            if _is_node_expr(expr, var_ctx):
                args = []
                for c in expr.children:
                    a = arith_to_cpp(c, var_ctx)
                    if isinstance(c, CInt):
                        a = f"nm->mkConstInt(Rational({c.val}))"
                    args.append(a)
                inner = ", ".join(args)
                return f"nm->mkNode(Kind::MULT, {{ {inner} }})"
            return "(" + " * ".join(arith_to_cpp(c, var_ctx) for c in expr.children) + ")"
        if expr.op == Op.PBVSIZE:
            arg = node_to_cpp(expr.children[0], var_ctx)
            return f"nm->mkNode(Kind::PBV_SIZE, {{ {arg} }})"

    raise NotImplementedError(
        f"arith_to_cpp: unhandled {type(expr).__name__}: {expr!r}")


###############################################################################
# Per-rule code block
###############################################################################

# Rule families gated by --pbv-rw-mw=MODE.  A rule whose name starts with one
# of these prefixes is emitted behind the corresponding bool member on the
# rewriter; every other rule is unconditional.
#
#   pbv-merge-*  mode base   shift-of-shift and nested-extension merge
#   pbv-c26-*    mode cav26  bitwise identities from the parabit rule set
#
# Rules without a family prefix may still be gated individually; see
# OPTION_GATED_RULES below.
#
# Adding a family means adding a prefix here, a member in the header template
# below, and a mode value in options/smt_options.toml.
OPTION_GATED_PREFIXES = {
    "pbv-merge-": "d_rwMerge",
    "pbv-c26-": "d_rwCav26",
}

# Individual rules that are opt-in but whose names do not carry a family
# prefix.  Keep this empty where a prefix will do; it exists for rules that
# belong to an existing RW_B group by name (and should keep that name) yet
# must not fire by default.
#
#   pbv-mul-two  strength-reduces `x * 2` to `x + x`.  It sits with
#                pbv-mul-one/pbv-mul-zero, so renaming it into a family would
#                misfile it, but it is not part of RW_B (SAT 2025 Appendix A):
#                leaving it unconditional silently changed the default
#                translation, since dropping the multiplication also drops the
#                piand and pow2 terms its integer encoding would have built.
OPTION_GATED_RULES = {
    "pbv-mul-two": "d_rwMerge",
}


def gated_guard(name: str) -> str | None:
    """The option member gating this rule, or None if it is unconditional."""
    if name in OPTION_GATED_RULES:
        return OPTION_GATED_RULES[name]
    for prefix, member in OPTION_GATED_PREFIXES.items():
        if name.startswith(prefix):
            return member
    return None


def gen_rule_block(rule: Rule, indent: str = "    ") -> list[str]:
    lines: list[str] = []
    lines.append(f"{indent}// Rule: {rule.name}")
    gate = gated_guard(rule.name)

    var_ctx: dict = {}
    structural_guards: list[str] = []

    try:
        walk_lhs(rule.lhs, "node", var_ctx, structural_guards)
    except NotImplementedError as exc:
        lines.append(f"{indent}// SKIPPED (LHS walk): {exc}")
        return lines

    # Semantic condition
    try:
        sem = cond_to_cpp(rule.cond, var_ctx)
    except NotImplementedError as exc:
        lines.append(f"{indent}// SKIPPED (condition): {exc}")
        return lines

    all_guards = structural_guards[:]
    if sem:
        all_guards.append(sem)
    if gate:
        all_guards.insert(0, gate)

    if all_guards:
        guard_expr = "\n" + f"{indent}    && ".join(all_guards)
        lines.append(f"{indent}if ({guard_expr})")
        lines.append(f"{indent}{{")
        body = indent + "  "
    else:
        body = indent

    # RHS
    try:
        rhs_cpp = node_to_cpp(rule.rhs, var_ctx)
    except NotImplementedError as exc:
        if all_guards:
            lines.append(f"{indent}}}")
        lines.append(f"{indent}// SKIPPED (RHS): {exc}")
        return lines

    enum = rule.get_enum().lower()
    lines.append(f"{body}Node rhs_{enum} = {rhs_cpp};")
    lines.append(f"{body}return RewriteResponse(REWRITE_AGAIN_FULL, rhs_{enum});")

    if all_guards:
        lines.append(f"{indent}}}")

    return lines


###############################################################################
# Manual raw C++ rules
#
# These rules cannot be expressed in the RARE DSL because their RHS requires
# the bit-width k = pbvsize(x), which is not structurally bound by the LHS.
# They are emitted verbatim into the generated implementation, after the
# RARE-derived rules.
#
# Source: Appendix A, "Bit-Precise Reasoning with Parametric Bit-Vectors"
###############################################################################

BOOL_HELPERS = r"""namespace {
/** Is this the all-zero constant `(int_to_pbv k 0)`? */
bool isZeroConst(TNode n)
{
  return n.getKind() == Kind::INT_TO_PBV && n.getNumChildren() == 2
         && n[1].isConst() && n[1].getConst<Rational>().sgn() == 0;
}
/** Does this node's top symbol act bitwise, so we can descend through it? */
bool isBitwise(TNode n)
{
  Kind k = n.getKind();
  return ((k == Kind::PBV_AND || k == Kind::PBV_OR || k == Kind::PBV_XOR)
          && n.getNumChildren() == 2)
         || (k == Kind::PBV_NOT && n.getNumChildren() == 1);
}
}  // namespace

bool TheoryPbvRewriter::boolLeaves(TNode n,
                                   std::vector<Node>& leaves,
                                   uint64_t cap)
{
  if (isZeroConst(n))
  {
    return true;  // the constant 0 contributes no variable
  }
  if (isBitwise(n))
  {
    for (size_t i = 0, m = n.getNumChildren(); i < m; ++i)
    {
      if (!boolLeaves(n[i], leaves, cap)) return false;
    }
    return true;
  }
  if (std::find(leaves.begin(), leaves.end(), Node(n)) == leaves.end())
  {
    if (leaves.size() >= cap) return false;
    leaves.emplace_back(n);
  }
  return true;
}

bool TheoryPbvRewriter::boolEval(TNode n,
                                 const std::vector<Node>& leaves,
                                 uint64_t asg)
{
  if (isZeroConst(n)) return false;
  Kind k = n.getKind();
  if (isBitwise(n))
  {
    if (k == Kind::PBV_NOT) return !boolEval(n[0], leaves, asg);
    bool a = boolEval(n[0], leaves, asg);
    bool b = boolEval(n[1], leaves, asg);
    if (k == Kind::PBV_AND) return a && b;
    if (k == Kind::PBV_OR) return a || b;
    return a != b;  // PBV_XOR
  }
  auto it = std::find(leaves.begin(), leaves.end(), Node(n));
  size_t idx = static_cast<size_t>(it - leaves.begin());
  return ((asg >> idx) & 1u) != 0;
}

"""

MANUAL_RULES_BODY = """\

  // ---------------------------------------------------------------------------
  // Shift merge across a zero extension (--pbv-rw-shift-zext-merge, off by default)
  //
  //   (pbvlshr (pzero_extend n (pbvlshr x y)) z)
  //       -> ite( (pbvadd y' z) >=u z ,  (pbvlshr x' (pbvadd y' z)) ,  0 )
  //   where x' = (pzero_extend n x), y' = (pzero_extend n y); dually for pbvshl.
  //
  // pbv-merge-lshr requires the two shifts to be ADJACENT, so it never matches a
  // multi-width goal: there the intermediate width sits between them as exactly
  // this zero extension. And the integer-level nested-division merge cannot help
  // either, because the int-blaster purifies the divisions into skolems while
  // translating, before the mod-reduction pass runs.
  //
  // Zero extension preserves the value, so the composition is x div 2^(y+z) --
  // the same identity pbv-merge-lshr proves for adjacent shifts, with the same
  // overflow guard, since y'+z is computed mod 2^|z| and can wrap.
  // ---------------------------------------------------------------------------
  if (d_rwShiftZext
      && (node.getKind() == Kind::PBV_LSHR || node.getKind() == Kind::PBV_SHL)
      && node.getNumChildren() == 2
      && node[0].getKind() == Kind::PBV_ZERO_EXTEND
      && node[0].getNumChildren() == 2
      && node[0][1].getKind() == node.getKind()
      && node[0][1].getNumChildren() == 2)
  {
    Kind sk = node.getKind();
    Node n0 = node[0][0];          // the extension amount
    Node x = node[0][1][0];
    Node y = node[0][1][1];
    Node z = node[1];
    Node xe = nm->mkNode(Kind::PBV_ZERO_EXTEND, {n0, x});
    Node ye = nm->mkNode(Kind::PBV_ZERO_EXTEND, {n0, y});
    Node sum = nm->mkNode(Kind::PBV_ADD, {ye, z});
    Node noOverflow = nm->mkNode(Kind::PBV_UGE, {sum, z});
    Node zero = nm->mkNode(Kind::INT_TO_PBV,
                           {nm->mkNode(Kind::PBV_SIZE, {z}),
                            nm->mkConstInt(Rational(0))});
    Node merged = nm->mkNode(sk, {xe, sum});
    return RewriteResponse(REWRITE_AGAIN_FULL,
                           nm->mkNode(Kind::ITE, {noOverflow, merged, zero}));
  }

  // ---------------------------------------------------------------------------
  // Boolean decision for bitwise equalities (--pbv-rw-bool, off by default)
  //
  // pbvand/pbvor/pbvxor/pbvnot act on each bit independently and identically,
  // so two such terms denote the same value at EVERY width exactly when the
  // Boolean functions they define over their leaves coincide. Enumerating the
  // leaf assignments therefore DECIDES this fragment -- which is what parabit
  // reaches only by saturating an e-graph with bidirectional xor_as_or_and and
  // and_distrib. A destructive rewriter cannot saturate, so it decides instead.
  //
  // A non-bitwise leaf is treated as an independent variable. That is sound for
  // concluding equality (agreement for every value of the leaf implies
  // agreement for its actual value) and merely costs completeness. Note the
  // converse is NOT available: differing tables cannot refute the goal, because
  // the leaves need not be independent, so this only ever returns true.
  // ---------------------------------------------------------------------------
  if (d_rwBool && node.getKind() == Kind::EQUAL && node.getNumChildren() == 2
      && node[0].getType().isPbv() && node[0] != node[1]
      && (isBitwise(node[0]) || isBitwise(node[1])))
  {
    std::vector<Node> leaves;
    if (boolLeaves(node[0], leaves, d_boolCap)
        && boolLeaves(node[1], leaves, d_boolCap) && !leaves.empty()
        && leaves.size() <= d_boolCap)
    {
      bool same = true;
      uint64_t rows = uint64_t(1) << leaves.size();
      for (uint64_t a = 0; a < rows; ++a)
      {
        if (boolEval(node[0], leaves, a) != boolEval(node[1], leaves, a))
        {
          same = false;
          break;
        }
      }
      if (same)
      {
        return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
      }
    }
  }

  // ---------------------------------------------------------------------------
  // De Morgan / negation normal form (--pbv-rw-nnf, off by default)
  //
  //   (pbvnot (pbvand x y))  ->  (pbvor  (pbvnot x) (pbvnot y))
  //   (pbvnot (pbvor  x y))  ->  (pbvand (pbvnot x) (pbvnot y))
  //
  // Terminating: each application moves a negation one level toward the leaves,
  // and pbv-not-idemp collapses the doubled ones, so the fixpoint is NNF.
  //
  // The term gets bigger, which is the whole point of it being opt-in -- what it
  // buys is a canonical DIRECTION. Goals in this family are written as
  // `(and (xor a ~0) (xor b ~0)) = (xor (or a b) ~0)`; --pbv-rw-mw=cav26 turns
  // `xor all-ones` into pbvnot, and then one side is `(and (not a) (not b))` and
  // the other `(not (or a b))`. Without De Morgan those are distinct terms and
  // the equality goes to the arithmetic solver as a piand query; with it, both
  // normalize to the same term and the goal closes in the rewriter.
  // ---------------------------------------------------------------------------
  if (d_rwNnf && node.getKind() == Kind::PBV_NOT && node.getNumChildren() == 1
      && (node[0].getKind() == Kind::PBV_AND
          || node[0].getKind() == Kind::PBV_OR)
      && node[0].getNumChildren() == 2)
  {
    Kind inner = node[0].getKind();
    Kind flipped = (inner == Kind::PBV_AND) ? Kind::PBV_OR : Kind::PBV_AND;
    Node nx = nm->mkNode(Kind::PBV_NOT, {node[0][0]});
    Node ny = nm->mkNode(Kind::PBV_NOT, {node[0][1]});
    return RewriteResponse(REWRITE_AGAIN_FULL,
                           nm->mkNode(flipped, {nx, ny}));
  }

  // ---------------------------------------------------------------------------
  // AC normalization for the associative-commutative operators
  // (--pbv-rw-ac, off by default): pbvand/pbvor/pbvxor and pbvadd/pbvmul.
  //
  // pbvand/pbvor/pbvxor are associative and commutative, but nothing in RW_B
  // canonicalizes the SHAPE of a nested chain. So `(x & y) & z` and
  // `x & (y & z)` stay distinct terms, and an equality between them survives
  // preprocessing and is handed to the arithmetic solver as a piand query --
  // which blows up once the leaves are symbolic-width extracts. parabit closes
  // exactly these by saturating with and.assoc / and.commute.
  //
  // Here: flatten the same-kind chain to its leaves, order them canonically,
  // drop duplicates for and/or (idempotent), and rebuild. pbvxor is ordered but
  // NOT deduplicated -- x xor x is 0, not x, and the binary case already has
  // its own rule.
  //
  // The chain is rebuilt RIGHT-ASSOCIATED and BINARY: PbvTypeRule asserts a
  // bitwise node has exactly two children, so an n-ary node must not be built.
  //
  // Width note: the encoding takes kappa(parent) = kappa(child 0), so moving a
  // different leaf into position 0 is only sound because the admissibility
  // constraints equate the operand widths, and the translation always asserts
  // them.
  if (d_rwAc
      && (node.getKind() == Kind::PBV_AND || node.getKind() == Kind::PBV_OR
          || node.getKind() == Kind::PBV_XOR || node.getKind() == Kind::PBV_ADD
          || node.getKind() == Kind::PBV_MULT))
  {
    Kind bk = node.getKind();
    // Flatten the same-kind chain into its leaves.
    std::vector<Node> leaves;
    std::vector<TNode> work{node};
    while (!work.empty())
    {
      TNode cur = work.back();
      work.pop_back();
      if (cur.getKind() == bk)
      {
        for (size_t ci = cur.getNumChildren(); ci-- > 0;)
        {
          work.push_back(cur[ci]);
        }
      }
      else
      {
        leaves.emplace_back(cur);
      }
    }
    if (leaves.size() >= 2)
    {
      std::vector<Node> norm = leaves;
      std::sort(norm.begin(), norm.end());
      // Idempotence holds for and/or only: x xor x is 0, x + x is 2x, and
      // x * x is x^2, so duplicates must survive everywhere else.
      if (bk == Kind::PBV_AND || bk == Kind::PBV_OR)
      {
        norm.erase(std::unique(norm.begin(), norm.end()), norm.end());
      }
      Node rebuilt;
      if (norm.size() == 1)
      {
        // Only reachable for and/or, where dedup collapsed every leaf to one.
        rebuilt = norm[0];
      }
      else
      {
        rebuilt = norm.back();
        for (size_t li = norm.size() - 1; li-- > 0;)
        {
          rebuilt = nm->mkNode(bk, {norm[li], rebuilt});
        }
      }
      if (rebuilt != node)
      {
        return RewriteResponse(REWRITE_AGAIN_FULL, rebuilt);
      }
    }
  }

  // ---------------------------------------------------------------------------
  // Raw C++ rules (width-dependent RHS; not expressible in RARE DSL)
  // Source: Appendix A, "Bit-Precise Reasoning with Parametric Bit-Vectors"
  //         Berger, Zohar, Niemetz, Preiner, Reynolds, Barrett, Tinelli (SAT 2025)
  // ---------------------------------------------------------------------------

  // pbv-add-self: (pbvadd x (pbvneg x)) => (int_to_pbv (pbvsize x) 0)
  if (node.getKind() == Kind::PBV_ADD && node.getNumChildren() == 2)
  {
    if (node[1].getKind() == Kind::PBV_NEG && node[0] == node[1][0])
    {
      Node width_add_self = nm->mkNode(Kind::PBV_SIZE, {node[0]});
      Node rhs_pbv_add_self =
          nm->mkNode(Kind::INT_TO_PBV, {width_add_self, nm->mkConstInt(Rational(0))});
      return RewriteResponse(REWRITE_AGAIN_FULL, rhs_pbv_add_self);
    }
  }

  // pbv-bitwise-not-or: (pbvor x (pbvnot x)) => (pbvnot (int_to_pbv (pbvsize x) 0))
  if (node.getKind() == Kind::PBV_OR && node.getNumChildren() == 2)
  {
    if (node[1].getKind() == Kind::PBV_NOT && node[0] == node[1][0])
    {
      Node width_not_or = nm->mkNode(Kind::PBV_SIZE, {node[0]});
      Node zero_not_or =
          nm->mkNode(Kind::INT_TO_PBV, {width_not_or, nm->mkConstInt(Rational(0))});
      Node rhs_pbv_bitwise_not_or = nm->mkNode(Kind::PBV_NOT, {zero_not_or});
      return RewriteResponse(REWRITE_AGAIN_FULL, rhs_pbv_bitwise_not_or);
    }
  }

  // pbv-xor-duplicate:   (pbvxor x x)          => (int_to_pbv (pbvsize x) 0)
  // pbv-xor-simplify-2:  (pbvxor x (pbvnot x)) => (pbvnot (int_to_pbv (pbvsize x) 0))
  if (node.getKind() == Kind::PBV_XOR && node.getNumChildren() == 2)
  {
    if (node[0] == node[1])
    {
      Node width_xor_dup = nm->mkNode(Kind::PBV_SIZE, {node[0]});
      Node rhs_pbv_xor_duplicate =
          nm->mkNode(Kind::INT_TO_PBV, {width_xor_dup, nm->mkConstInt(Rational(0))});
      return RewriteResponse(REWRITE_AGAIN_FULL, rhs_pbv_xor_duplicate);
    }
    if (node[1].getKind() == Kind::PBV_NOT && node[0] == node[1][0])
    {
      Node width_xor_s2 = nm->mkNode(Kind::PBV_SIZE, {node[0]});
      Node zero_xor_s2 =
          nm->mkNode(Kind::INT_TO_PBV, {width_xor_s2, nm->mkConstInt(Rational(0))});
      Node rhs_pbv_xor_simplify_2 = nm->mkNode(Kind::PBV_NOT, {zero_xor_s2});
      return RewriteResponse(REWRITE_AGAIN_FULL, rhs_pbv_xor_simplify_2);
    }
  }

  // pbv-urem-self: (pbvurem x x) => (int_to_pbv (pbvsize x) 0)
  if (node.getKind() == Kind::PBV_UREM)
  {
    if (node[0] == node[1])
    {
      Node width_urem_self = nm->mkNode(Kind::PBV_SIZE, {node[0]});
      Node rhs_pbv_urem_self =
          nm->mkNode(Kind::INT_TO_PBV, {width_urem_self, nm->mkConstInt(Rational(0))});
      return RewriteResponse(REWRITE_AGAIN_FULL, rhs_pbv_urem_self);
    }
  }


"""


###############################################################################
# Top-level kind of rule LHS
###############################################################################

def lhs_kind(rule: Rule):
    return rule.lhs.op.kind if isinstance(rule.lhs, App) else None


###############################################################################
# Static header content
###############################################################################

HEADER_CONTENT = """\
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
 * Theory PBV rewriter.
 *
 * Applies the RW_B rewrite rule set (Appendix A) from:
 *   "Bit-Precise Reasoning with Parametric Bit-Vectors"
 *   Berger, Zohar, Niemetz, Preiner, Reynolds, Barrett, Tinelli (SAT 2025)
 *
 * The implementation of postRewrite is auto-generated by:
 *   python3 src/theory/pbv/generate_rewriter.py
 * into theory_pbv_rewriter.cpp.  Do not edit that file by hand.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__PBV__THEORY_PBV_REWRITER_H
#define CVC5__THEORY__PBV__THEORY_PBV_REWRITER_H

#include "options/smt_options.h"
#include "theory/theory_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace pbv {

class TheoryPbvRewriter : public TheoryRewriter {
 public:
  /**
   * @param rwMw value of --pbv-rw-mw=MODE, selecting which opt-in rule
   * families to apply:
   *   none   neither (default)
   *   base   the `pbv-merge-*` rules: shift-of-shift merge, nested
   *          extension merge
   *   cav26  the `pbv-c26-*` rules: bitwise identities adapted from the
   *          parabit rule set
   *   all    both
   */
  TheoryPbvRewriter(NodeManager* nm,
                    options::PbvRwMwMode rwMw = options::PbvRwMwMode::NONE,
                    bool rwAc = false,
                    bool rwNnf = false,
                    bool rwBool = false,
                    uint64_t boolCap = 12,
                    bool rwShiftZext = false)
      : TheoryRewriter(nm),
        d_rwMerge(rwMw == options::PbvRwMwMode::BASE
                  || rwMw == options::PbvRwMwMode::ALL),
        d_rwCav26(rwMw == options::PbvRwMwMode::CAV26
                  || rwMw == options::PbvRwMwMode::ALL),
        d_rwAc(rwAc),
        d_rwNnf(rwNnf),
        d_rwBool(rwBool),
        d_boolCap(boolCap),
        d_rwShiftZext(rwShiftZext)
  {
  }

  /**
   * Post-rewrite: apply the full RW_B rule set (Appendix A).
   * Returns REWRITE_AGAIN_FULL when a rule fires; REWRITE_DONE otherwise.
   * Implementation is auto-generated into theory_pbv_rewriter.cpp.
   */
  RewriteResponse postRewrite(TNode node) override;

  /**
   * Pre-rewrite: no rules applied at this stage.
   */
  RewriteResponse preRewrite(TNode node) override {
    return RewriteResponse(REWRITE_DONE, node);
  }

 private:
  /** --pbv-rw-mw=base|all: enable the `pbv-merge-*` rules. */
  bool d_rwMerge;
  /** --pbv-rw-mw=cav26|all: enable the `pbv-c26-*` rules. */
  bool d_rwCav26;
  /** --pbv-rw-ac: AC-normalize pbvand/pbvor/pbvxor. */
  bool d_rwAc;
  /** --pbv-rw-nnf: push pbvnot inward through pbvand/pbvor (De Morgan). */
  bool d_rwNnf;
  /** --pbv-rw-bool: decide bitwise equalities by Boolean evaluation. */
  bool d_rwBool;
  /** --pbv-rw-bool-cap: give up past this many distinct leaves. */
  uint64_t d_boolCap;
  /** --pbv-rw-shift-zext-merge: merge shifts across a zero extension. */
  bool d_rwShiftZext;

  /** Gather the distinct non-bitwise leaves of a bitwise term. */
  static bool boolLeaves(TNode n, std::vector<Node>& leaves, uint64_t cap);
  /** Evaluate a bitwise term under an assignment (bit i of `asg` per leaf). */
  static bool boolEval(TNode n, const std::vector<Node>& leaves, uint64_t asg);
};

}  // namespace pbv
}  // namespace theory
}  // namespace cvc5::internal

#endif  // CVC5__THEORY__PBV__THEORY_PBV_REWRITER_H
"""


###############################################################################
# Main
###############################################################################

def generate(output_dir: Path = None):
    # Resolve output directory: CLI-supplied or the script's own directory.
    out = Path(output_dir) if output_dir is not None else SCRIPT_DIR
    out.mkdir(parents=True, exist_ok=True)
    header_file = out / "theory_pbv_rewriter.h"
    impl_file   = out / "theory_pbv_rewriter.cpp"

    parser = Parser()
    with open(REWRITES_FILE) as fh:
        rules = parser.parse_rules(fh.read())

    by_kind: dict[str, list] = defaultdict(list)
    skipped = []
    for rule in rules:
        k = lhs_kind(rule)
        if k:
            by_kind[k].append(rule)
        else:
            skipped.append(rule)

    if skipped:
        print(f"WARNING: {len(skipped)} rules skipped (no top-level kind): "
              f"{[r.name for r in skipped]}", file=sys.stderr)

    body_lines: list[str] = []
    for kind in sorted(by_kind):
        body_lines.append(f"  // --- Kind::{kind} ---")
        body_lines.append(f"  if (node.getKind() == Kind::{kind})")
        body_lines.append(f"  {{")
        for rule in by_kind[kind]:
            for line in gen_rule_block(rule, "    "):
                body_lines.append(line)
            body_lines.append("")
        body_lines.append(f"  }}  // Kind::{kind}")
        body_lines.append("")

    body = "\n".join(body_lines)

    impl = (
        "/******************************************************************************\n"
        " * AUTO-GENERATED by src/theory/pbv/generate_rewriter.py\n"
        " *\n"
        " * DO NOT EDIT BY HAND.  Re-generate by running:\n"
        " *   python3 src/theory/pbv/generate_rewriter.py\n"
        " *\n"
        " * Implements RW_B (Appendix A) from:\n"
        " *   \"Bit-Precise Reasoning with Parametric Bit-Vectors\"\n"
        " *   Berger, Zohar, Niemetz, Preiner, Reynolds, Barrett, Tinelli (SAT 2025)\n"
        " *\n"
        " * Source rules: src/theory/pbv/rewrites  (RARE DSL)\n"
        " * Parser:       src/rewriter/rw_parser.py\n"
        " *\n"
        " * Design principles (Section 4.1):\n"
        " *   (i)  No rule introduces a new bitwise PBV operator.\n"
        " *   (ii) The integer translation must not increase mod/pow2 occurrences.\n"
        " ******************************************************************************/\n"
        "\n"
        "#include \"theory/pbv/theory_pbv_rewriter.h\"\n"
        "\n"
        "#include <algorithm>\n"
        "#include <vector>\n"
        "\n"
        "#include \"expr/node.h\"\n"
        "#include \"expr/node_manager.h\"\n"
        "#include \"theory/rewriter.h\"\n"
        "#include \"util/rational.h\"\n"
        "\n"
        "namespace cvc5::internal {\n"
        "namespace theory {\n"
        "namespace pbv {\n"
        "\n"
        f"{BOOL_HELPERS}"
        "RewriteResponse TheoryPbvRewriter::postRewrite(TNode node)\n"
        "{\n"
        "  NodeManager* nm = d_nm;\n"
        f"{body}"
        f"{MANUAL_RULES_BODY}"
        "  return RewriteResponse(REWRITE_DONE, node);\n"
        "}\n"
        "\n"
        "}  // namespace pbv\n"
        "}  // namespace theory\n"
        "}  // namespace cvc5::internal\n"
    )

    # Write header (stable class declaration)
    with open(header_file, "w") as fh:
        fh.write(HEADER_CONTENT)

    # Write implementation (auto-generated rule dispatch)
    with open(impl_file, "w") as fh:
        fh.write(impl)

    print(f"Generated header : {header_file}")
    print(f"Generated impl   : {impl_file}")
    print(f"Rules parsed: {len(rules)}")
    print(f"Kinds covered ({len(by_kind)}): {sorted(by_kind)}")
    if skipped:
        print(f"Skipped: {[r.name for r in skipped]}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(
        description="Generate TheoryPbvRewriter .h/.cpp from the RARE rewrites file."
    )
    ap.add_argument(
        "--output-dir",
        metavar="DIR",
        default=None,
        help="Directory to write the generated files into "
             "(default: same directory as this script).",
    )
    args = ap.parse_args()
    generate(output_dir=args.output_dir)
