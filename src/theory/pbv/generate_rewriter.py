#!/usr/bin/env python3
###############################################################################
# generate_rewriter.py
#
# Parses a RARE rewrites file of the PBV theory and emits two C++ files. The
# --profile selects which:
#
#   pbv    src/theory/pbv/rewrites        -> theory_pbv_rewriter.{h,cpp}
#          class TheoryPbvRewriter, the theory rewriter of PBV (RW_B,
#          Appendix A of the paper below)
#   piand  src/theory/pbv/rewrites-piand  -> theory_piand_rewriter.{h,cpp}
#          free function pbv::rewritePiandRare, called by
#          ArithRewriter::postRewritePIAnd (--piand-rare-rewrites)
#   exp    src/theory/pbv/rewrites-exp    -> theory_exp_rewriter.{h,cpp}
#          free function pbv::rewriteExpRare, called by
#          ArithRewriter::postRewriteExp (--arith-exp-rare-rewrites)
#
# The piand and exp kinds belong to the arithmetic theory, so their rules
# cannot live in a TheoryRewriter of their own; the generated function returns
# the rewritten node, or a null node when no rule fires, and the arith rewriter
# decides what to do with it.
#
# from: "Bit-Precise Reasoning with Parametric Bit-Vectors"
#       Berger, Zohar, Niemetz, Preiner, Reynolds, Barrett, Tinelli (SAT 2025)
#
# Both files are build products: the build writes them to build/src/theory/pbv
# and neither belongs in the source tree.
#
# Usage (from the cvc5 source root):
#   python3 src/theory/pbv/generate_rewriter.py --output-dir /path/to/dir
#   python3 src/theory/pbv/generate_rewriter.py --profile piand --output-dir DIR
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
    from node import Op, Var, CBool, CInt, CRational, CString, App, Placeholder
    from rule import Rule
    from mkrewrites import gen_kind, gen_mk_node, validate_rule
except ImportError as exc:
    sys.exit(
        f"ERROR: Cannot import cvc5 rewriter modules from {REWRITER_DIR}.\n"
        f"Underlying error: {exc}"
    )


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

# Kinds that take two OR MORE operands (kinds.toml: children = "2:").
NARY_KINDS = {
    "PBV_AND", "PBV_OR", "PBV_XOR", "PBV_ADD", "PBV_MULT", "PBV_CONCAT",
    "ADD", "MULT", "NONLINEAR_MULT", "AND", "OR",
}


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

    if (isinstance(pattern, App) and pattern.op == Op.NEG
            and isinstance(pattern.children[0], CInt)):
        # The rewritten form of (- c) is the constant -c, never a NEG node.
        guards.append(
            f"({accessor}.isConst() && "
            f"{accessor}.getConst<Rational>() == Rational(-{pattern.children[0].val}))")
        return

    if isinstance(pattern, (CBool, CRational, CString)):
        # For completeness – not expected in PBV rules
        guards.append(f"({accessor} /* literal-guard */ )")
        return

    if isinstance(pattern, App):
        if accessor != "node":
            guards.append(f"({accessor}.getKind() == Kind::{gen_kind(pattern.op)})")
        # An n-ary operator matches only with the pattern's exact arity:
        # without this, `(pbvadd x 0)` would match `(pbvadd x 0 z)` through
        # node[0]/node[1] and the rewrite would silently drop z.
        if gen_kind(pattern.op) in NARY_KINDS:
            guards.append(
                f"({accessor}.getNumChildren() == {len(pattern.children)})")
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
    """
    Build a term with the proof generator's gen_mk_node: its definitions map
    gives each variable the accessor that matched it, such as node[1][0].
    """
    check_vars_bound(expr, var_ctx)
    return gen_mk_node(var_ctx, expr)


def check_vars_bound(expr, var_ctx: dict) -> None:
    """gen_mk_node prints an unknown variable as is, which fails in the C++."""
    if isinstance(expr, Var) and expr not in var_ctx:
        raise NotImplementedError(
            f"variable '{expr.name}' is not bound by the left-hand side")
    for child in expr.children:
        check_vars_bound(child, var_ctx)


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
            # On terms, == is structural equality: it implies the condition,
            # so it is a sound (if incomplete) test. <, <=, >, >= on Nodes
            # would compare node ids, not values.
            if cond.op != Op.EQ and _is_node_expr(cond, var_ctx):
                raise NotImplementedError(
                    f"inequality on terms needs the evaluated conditions of "
                    f"the piand/exp profiles: {cond!r}")
            lhs = arith_to_cpp(cond.children[0], var_ctx)
            rhs = arith_to_cpp(cond.children[1], var_ctx)
            return f"{lhs} {op_map[cond.op]} {rhs}"

        if cond.op == Op.NOT:
            # !(a == b) on terms holds for distinct terms of equal value.
            if _is_node_expr(cond, var_ctx):
                raise NotImplementedError(
                    f"negation on terms needs the evaluated conditions of "
                    f"the piand/exp profiles: {cond!r}")
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
    check_vars_bound(expr, var_ctx)
    if _is_node_expr(expr, var_ctx):
        return gen_mk_node(var_ctx, expr)

    if isinstance(expr, CInt):
        return str(expr.val)

    if isinstance(expr, App):
        args = [arith_to_cpp(c, var_ctx) for c in expr.children]
        if expr.op == Op.NEG:
            return f"(-{args[0]})"
        if expr.op in (Op.ADD, Op.SUB, Op.MULT):
            separator = {Op.ADD: " + ", Op.SUB: " - ", Op.MULT: " * "}[expr.op]
            return "(" + separator.join(args) + ")"

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
    "pbv-andn-": "d_rwAndNot",
    "pbv-orn-": "(d_rwOrNot && !d_rwOrNotSimple)",
    "pbv-orns-": "(d_rwOrNot && d_rwOrNotSimple)",
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


# Rules (or families, by prefix) that --pbv-rewrites-min also enables, on top
# of their own gate: the rewriter's share of the RW_B table, without the rest
# of the pbv-c26-* family.
MIN_RULES = ("pbv-c26-xor-allones", "pbv-c26-not-plus-one", "pbv-andn-")


def gated_guard(name: str) -> str | None:
    """The option member gating this rule, or None if it is unconditional."""
    member = OPTION_GATED_RULES.get(name)
    if member is None:
        for prefix, m in OPTION_GATED_PREFIXES.items():
            if name.startswith(prefix):
                member = m
                break
    if member is not None and name.startswith(MIN_RULES):
        return f"({member} || d_rwMin)"
    return member


def ret_rewrite_response(var: str) -> str:
    """Return statement of the pbv profile: a TheoryRewriter response."""
    return f"return RewriteResponse(REWRITE_AGAIN_FULL, {var});"


def cond_eval_cpp(cond, var_ctx: dict) -> str:
    """
    Condition of the piand/exp profiles: build the condition term and require
    that it EVALUATES to true. A condition on a free term (e.g. t >= 0 with
    symbolic t) does not evaluate, so the rule does not fire -- the rewriter
    never assumes an unproved side condition.
    """
    if isinstance(cond, CBool):
        return "" if cond.val else "false"
    check_vars_bound(cond, var_ctx)
    return f"rareCondHolds({gen_mk_node(var_ctx, cond)})"


def ret_node(var: str) -> str:
    """Return statement of the piand/exp profiles: the bare rewritten node."""
    return f"return {var};"


def gen_rule_block(rule: Rule, indent: str = "    ", gate_fn=gated_guard,
                   ret_fn=ret_rewrite_response,
                   cond_fn=cond_to_cpp) -> list[str]:
    lines: list[str] = []
    lines.append(f"{indent}// Rule: {rule.name}")
    gate = gate_fn(rule.name)

    var_ctx: dict = {}
    structural_guards: list[str] = []

    try:
        walk_lhs(rule.lhs, "node", var_ctx, structural_guards)
    except NotImplementedError as exc:
        lines.append(f"{indent}// SKIPPED (LHS walk): {exc}")
        return lines

    # Semantic condition
    try:
        sem = cond_fn(rule.cond, var_ctx)
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
    lines.append(f"{body}{ret_fn(f'rhs_{enum}')}")

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
    return gen_kind(rule.lhs.op) if isinstance(rule.lhs, App) else None


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
                    bool rwShiftZext = false,
                    bool rwAndNot = false,
                    bool rwOrNot = false,
                    bool rwOrNotSimple = false,
                    bool rwMin = false)
      : TheoryRewriter(nm),
        d_rwMerge(rwMw == options::PbvRwMwMode::BASE
                  || rwMw == options::PbvRwMwMode::BASE_CAV26),
        d_rwCav26(rwMw == options::PbvRwMwMode::CAV26
                  || rwMw == options::PbvRwMwMode::BASE_CAV26
                  || rwMw == options::PbvRwMwMode::ALL),
        d_rwAc(rwAc),
        d_rwNnf(rwNnf),
        d_rwBool(rwBool),
        d_boolCap(boolCap),
        d_rwShiftZext(rwShiftZext),
        d_rwAndNot(rwAndNot),
        d_rwOrNot(rwOrNot),
        d_rwOrNotSimple(rwOrNotSimple),
        d_rwMin(rwMin)
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
  /** --pbv-rw-and-not: the `pbv-andn-*` rules, x & ~y -> x - (x & y). */
  bool d_rwAndNot;
  /**
   * --pbv-rw-or-not: the `pbv-orn-*` rules, x | ~y -> ~0 - y + (x & y), or
   * with d_rwOrNotSimple the `pbv-orns-*` rules, x | ~y -> ~y + (x & y).
   */
  bool d_rwOrNot;
  /** --pbv-rw-or-not-simple: which of the two or-not forms is used. */
  bool d_rwOrNotSimple;
  /**
   * --pbv-rewrites-min: the rules of the RW_B table that live here
   * (xor-ones, not-plus-one, and-not), without the rest of their families.
   */
  bool d_rwMin;

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
# Rule-only rewriters (piand, exp profiles)
#
# A free function per file: the kinds belong to the arithmetic theory, whose
# rewriter calls the function and keeps control of the response.
###############################################################################

FUNC_HEADER_TEMPLATE = """\
/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * RARE rewrites for {what}.
 *
 * AUTO-GENERATED by src/theory/pbv/generate_rewriter.py --profile {profile}.
 * The rules are in src/theory/pbv/{rewrites}; the implementation is generated
 * into {base}.cpp. Do not edit either file by hand.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__PBV__{guard}_H
#define CVC5__THEORY__PBV__{guard}_H

#include "expr/node.h"

namespace cvc5::internal {{

class NodeManager;

namespace theory {{
namespace pbv {{

/**
 * Apply the first rule of src/theory/pbv/{rewrites} whose left-hand side
 * matches node, and return its right-hand side; return the null node if no
 * rule matches. The children of node are expected to be rewritten already.
 */
Node {func}(NodeManager* nm, TNode node);

}}  // namespace pbv
}}  // namespace theory
}}  // namespace cvc5::internal

#endif  // CVC5__THEORY__PBV__{guard}_H
"""

FUNC_IMPL_TEMPLATE = """\
/******************************************************************************
 * AUTO-GENERATED by src/theory/pbv/generate_rewriter.py --profile {profile}
 *
 * DO NOT EDIT BY HAND.  The build regenerates this file from the rules.
 *
 * Source rules: src/theory/pbv/{rewrites}  (RARE DSL)
 * Parser:       src/rewriter/rw_parser.py
 ******************************************************************************/

#include "theory/pbv/{base}.h"

#include "expr/node.h"
#include "expr/node_manager.h"
#include "theory/evaluator.h"
#include "util/rational.h"

namespace cvc5::internal {{
namespace theory {{
namespace pbv {{

namespace {{

/**
 * True iff the side condition c evaluates to true. A condition on free terms
 * does not evaluate, and then the rule does not fire.
 */
[[maybe_unused]] bool rareCondHolds(Node c)
{{
  Evaluator eval(nullptr);
  Node v = eval.eval(c, {{}}, {{}});
  return !v.isNull() && v.isConst() && v.getType().isBoolean()
         && v.getConst<bool>();
}}

}}  // namespace

Node {func}(NodeManager* nm, TNode node)
{{
{body}
  return Node::null();
}}

}}  // namespace pbv
}}  // namespace theory
}}  // namespace cvc5::internal
"""


class Profile:
    def __init__(self, name, rewrites, base, kinds=None, func=None, what=None):
        self.name = name
        self.rewrites = rewrites    # file name under src/theory/pbv
        self.base = base            # output file stem
        self.kinds = kinds          # allowed LHS kinds; None = any
        self.func = func            # generated function (None: TheoryPbvRewriter)
        self.what = what


PROFILES = {
    "pbv": Profile("pbv", "rewrites", "theory_pbv_rewriter"),
    "piand": Profile("piand", "rewrites-piand", "theory_piand_rewriter",
                     kinds={"PIAND"}, func="rewritePiandRare",
                     what="the parametric integer AND (piand)"),
    "exp": Profile("exp", "rewrites-exp", "theory_exp_rewriter",
                   kinds={"EXP", "INTS_DIVISION", "INTS_MODULUS"},
                   func="rewriteExpRare",
                   what="integer exponentiation (exp, **) and the div/mod "
                        "identities on its powers"),
}


def func_header(p: Profile) -> str:
    return FUNC_HEADER_TEMPLATE.format(
        what=p.what, profile=p.name, rewrites=p.rewrites, base=p.base,
        guard=p.base.upper(), func=p.func)


###############################################################################
# Main
###############################################################################

def generate(output_dir: Path, only: str = None, profile: str = "pbv",
             rewrites: Path = None):
    p = PROFILES[profile]
    rewrites_file = Path(rewrites) if rewrites else SCRIPT_DIR / p.rewrites
    out = Path(output_dir)
    out.mkdir(parents=True, exist_ok=True)
    header_file = out / f"{p.base}.h"
    impl_file   = out / f"{p.base}.cpp"

    if only != "impl":
        with open(header_file, "w") as fh:
            fh.write(HEADER_CONTENT if p.func is None else func_header(p))
        print(f"Generated header : {header_file}")
    if only == "header":
        return

    parser = Parser()
    with open(rewrites_file) as fh:
        rules = parser.parse_rules(fh.read())

    # A rule that cannot be translated must stop the build: otherwise it stays
    # in the proof database but silently never fires in the solver.
    errors: list[str] = []
    seen_names: set[str] = set()
    by_kind: dict[str, list] = defaultdict(list)
    for rule in rules:
        validate_rule(rule)
        if rule.name in seen_names:
            errors.append(f"{rule.name}: duplicate rule name")
        seen_names.add(rule.name)
        k = lhs_kind(rule)
        if not k:
            errors.append(f"{rule.name}: left-hand side has no top-level "
                          f"operator to match on")
        elif p.kinds is not None and k not in p.kinds:
            errors.append(f"{rule.name}: left-hand side is {k}, but the "
                          f"{p.name} rewriter is only called on "
                          f"{', '.join(sorted(p.kinds))}, so it would never fire")
        else:
            by_kind[k].append(rule)

    body_lines: list[str] = []
    for kind in sorted(by_kind):
        body_lines.append(f"  // --- Kind::{kind} ---")
        body_lines.append(f"  if (node.getKind() == Kind::{kind})")
        body_lines.append(f"  {{")
        for rule in by_kind[kind]:
            if p.func is None:
                block = gen_rule_block(rule, "    ")
            else:
                block = gen_rule_block(rule, "    ", gate_fn=lambda _: None,
                                       ret_fn=ret_node, cond_fn=cond_eval_cpp)
            for line in block:
                body_lines.append(line)
                if "// SKIPPED " in line:
                    errors.append(f"{rule.name}: {line.strip()[3:]}")
            body_lines.append("")
        body_lines.append(f"  }}  // Kind::{kind}")
        body_lines.append("")

    if errors:
        for error in errors:
            print(f"ERROR: {rewrites_file}: {error}", file=sys.stderr)
        sys.exit(1)

    body = "\n".join(body_lines)

    if p.func is not None:
        with open(impl_file, "w") as fh:
            fh.write(FUNC_IMPL_TEMPLATE.format(
                profile=p.name, rewrites=p.rewrites, base=p.base, func=p.func,
                body=body.rstrip("\n")))
        print(f"Generated impl   : {impl_file}")
        print(f"Rules parsed: {len(rules)}")
        return

    impl = (
        "/******************************************************************************\n"
        " * AUTO-GENERATED by src/theory/pbv/generate_rewriter.py\n"
        " *\n"
        " * DO NOT EDIT BY HAND.  The build regenerates this file from the rules.\n"
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

    # Write implementation (auto-generated rule dispatch)
    with open(impl_file, "w") as fh:
        fh.write(impl)

    print(f"Generated impl   : {impl_file}")
    print(f"Rules parsed: {len(rules)}")
    print(f"Kinds covered ({len(by_kind)}): {sorted(by_kind)}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(
        description="Generate a PBV-theory rewriter .h/.cpp from a RARE rewrites file."
    )
    ap.add_argument(
        "--profile",
        choices=sorted(PROFILES),
        default="pbv",
        help="Which rewriter to generate (default: pbv). piand and exp read "
             "rewrites-piand / rewrites-exp and emit a free function that the "
             "arithmetic rewriter calls.",
    )
    ap.add_argument(
        "--rewrites",
        metavar="FILE",
        help="RARE file to read instead of the profile's default.",
    )
    ap.add_argument(
        "--output-dir",
        metavar="DIR",
        required=True,
        help="Directory to write the generated files into.",
    )
    ap.add_argument(
        "--only",
        choices=["header", "impl"],
        help="Write just one file. The build uses this because the header does "
             "not depend on the rules: rewriting it on every rule edit would "
             "recompile everything that includes it.",
    )
    args = ap.parse_args()
    generate(args.output_dir, args.only, args.profile, args.rewrites)
