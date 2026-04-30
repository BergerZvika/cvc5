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

def gen_rule_block(rule: Rule, indent: str = "    ") -> list[str]:
    lines: list[str] = []
    lines.append(f"{indent}// Rule: {rule.name}")

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

MANUAL_RULES_BODY = """\

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

#include "theory/theory_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace pbv {

class TheoryPbvRewriter : public TheoryRewriter {
 public:
  TheoryPbvRewriter(NodeManager* nm) : TheoryRewriter(nm) {}

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
        "#include \"expr/node.h\"\n"
        "#include \"expr/node_manager.h\"\n"
        "#include \"theory/rewriter.h\"\n"
        "#include \"util/rational.h\"\n"
        "\n"
        "namespace cvc5::internal {\n"
        "namespace theory {\n"
        "namespace pbv {\n"
        "\n"
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
