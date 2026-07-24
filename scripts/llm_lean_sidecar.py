#!/usr/bin/env python3
"""Small LLM/Lean sidecar for SAIR true-case proof experiments.

This is intentionally not part of the production solver. It is a wind-tunnel for
testing the interface between an LLM and the existing mechanical verifier:

  1. load one problem;
  2. ask for, or accept, a Lean tactic body after `intro G _ h`;
  3. apply light syntax/scaffolding cleanup;
  4. verify with the official judge;
  5. if it fails, feed back the cleaned code plus a compact Lean error.

Examples:

  # Print the prompt, no network.
  python3 scripts/llm_lean_sidecar.py --problem-id normal_0121 --dry-run

  # Verify a candidate proof body from a file, no LLM.
  python3 scripts/llm_lean_sidecar.py --problem-id normal_0121 \
    --candidate-proof-file /tmp/proof.lean

  # Call a configured LLM with two repair rounds.
  zsh -lc 'python3 scripts/llm_lean_sidecar.py --problem-id hard2_0107 \
    --config official-stage2/pipeline/results/llm_openrouter_fast_config.json \
    --rounds 3'
"""

from __future__ import annotations

import argparse
import difflib
import itertools
import json
import math
import os
import random
import re
import sys
import time
from datetime import datetime
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
OFFICIAL = ROOT / "official-stage2"
PROBLEM_DIR = OFFICIAL / "examples" / "problems"

sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(OFFICIAL))

import baby_solver as solver_core  # noqa: E402
import openai  # noqa: E402
from openai import OpenAI  # noqa: E402
from judge.verify import JudgeConfig, verify_answer, _static_lake_lean_path  # noqa: E402
from pipeline.proxy import _call_llm, load_config  # noqa: E402


if not os.environ.get("JUDGE_LEAN_PATH"):
    static_lean_path = _static_lake_lean_path()
    if static_lean_path:
        os.environ["JUDGE_LEAN_PATH"] = static_lean_path


def load_problem(problem_id: str | None, problem_file: Path | None) -> dict[str, Any]:
    if problem_file is not None:
        text = problem_file.read_text(encoding="utf-8").strip()
        if not text:
            raise SystemExit(f"empty problem file: {problem_file}")
        if text.startswith("["):
            data = json.loads(text)
            if not data:
                raise SystemExit(f"problem array is empty: {problem_file}")
            if problem_id is None:
                return data[0]
            for item in data:
                if item.get("id") == problem_id:
                    return item
            raise SystemExit(f"problem id {problem_id!r} not found in {problem_file}")
        rows = [json.loads(line) for line in text.splitlines() if line.strip()]
        if problem_id is None:
            return rows[0]
        for item in rows:
            if item.get("id") == problem_id:
                return item
        raise SystemExit(f"problem id {problem_id!r} not found in {problem_file}")

    if problem_id is None:
        raise SystemExit("provide --problem-id or --problem-file")

    for path in sorted(PROBLEM_DIR.glob("*.jsonl")):
        for line in path.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            item = json.loads(line)
            if item.get("id") == problem_id:
                return item
    for path in sorted(PROBLEM_DIR.glob("*.json")):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue
        if isinstance(data, list):
            for item in data:
                if isinstance(item, dict) and item.get("id") == problem_id:
                    return item
    raise SystemExit(f"problem id {problem_id!r} not found under {PROBLEM_DIR}")


def parse_problem(problem: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    h_eq = solver_core.parse_equation(solver_core.normalize(problem["equation1"]))
    g_eq = solver_core.parse_equation(solver_core.normalize(problem["equation2"]))
    return h_eq, g_eq


def hypothesis_schema(h_eq: dict[str, Any]) -> str:
    placeholders = ["A", "B", "C", "D", "E", "F", "U", "V", "W"]
    if len(h_eq["variables"]) > len(placeholders):
        placeholders.extend(f"T{i}" for i in range(len(placeholders), len(h_eq["variables"])))
    var_map = {
        var: placeholders[i]
        for i, var in enumerate(h_eq["variables"])
    }
    args = " ".join(var_map[var] for var in h_eq["variables"])
    lhs = solver_core.term_to_str_subst(h_eq["lhs"], var_map)
    rhs = solver_core.term_to_str_subst(h_eq["rhs"], var_map)
    return (
        f"Exact h schema: `h {args}` has type\n"
        f"  {lhs} = {rhs}\n"
        "Here A, B, C, ... may be any current variables or compound `◇` terms. "
        "Every typed `have` must match this schema exactly; do not rewrite the "
        "right side in your head before Lean has an equality proving it."
    )


def _unique(items: list[str]) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for item in items:
        if item not in seen:
            seen.add(item)
            out.append(item)
    return out


def _term_vars(t: Any) -> list[str]:
    if t[0] == "var":
        return [t[1]]
    return _term_vars(t[1]) + _term_vars(t[2])


def _leftmost_var(t: Any) -> str | None:
    if t[0] == "var":
        return t[1]
    return _leftmost_var(t[1])


def _goal_vars_by_relevance(g_eq: dict[str, Any]) -> list[str]:
    text_vars = _term_vars(g_eq["lhs"]) + _term_vars(g_eq["rhs"])
    counts = {v: text_vars.count(v) for v in g_eq["variables"]}
    return sorted(g_eq["variables"], key=lambda v: (-counts.get(v, 0), g_eq["variables"].index(v)))


def _small_goal_compounds(g_eq: dict[str, Any], limit: int = 8) -> list[str]:
    terms = solver_core.compound_subterms(g_eq["lhs"]) + solver_core.compound_subterms(g_eq["rhs"])
    ordered = sorted(terms, key=lambda t: (solver_core.term_size(t), solver_core.term_to_str(t)))
    return _unique([solver_core.term_to_str(t) for t in ordered])[:limit]


def _unary_terms(v: str) -> list[str]:
    return [
        f"({v} ◇ {v})",
        f"(({v} ◇ {v}) ◇ {v})",
        f"({v} ◇ ({v} ◇ {v}))",
    ]


def render_h_type(h_eq: dict[str, Any], args: tuple[str, ...]) -> tuple[str, str]:
    var_map = {
        var: args[i]
        for i, var in enumerate(h_eq["variables"])
    }
    return (
        solver_core.term_to_str_subst(h_eq["lhs"], var_map),
        solver_core.term_to_str_subst(h_eq["rhs"], var_map),
    )


def candidate_h_args(h_eq: dict[str, Any], g_eq: dict[str, Any], limit: int) -> list[tuple[str, ...]]:
    if limit <= 0 or not h_eq["variables"]:
        return []
    nargs = len(h_eq["variables"])
    goal_vars = g_eq["variables"] or ["x"]
    relevant_vars = _goal_vars_by_relevance(g_eq) or goal_vars
    endpoint_vars = _unique([
        v for v in (
            _leftmost_var(g_eq["lhs"]),
            _leftmost_var(g_eq["rhs"]),
        )
        if v
    ])
    small_compounds = _small_goal_compounds(g_eq)
    primary_terms = _unique(endpoint_vars + small_compounds + goal_vars)
    secondary_terms = _unique(
        small_compounds[:2]
        + [term for v in relevant_vars for term in _unary_terms(v)]
        + small_compounds[2:]
        + relevant_vars
        + goal_vars
    )

    tuples: list[tuple[str, ...]] = []
    seen: set[tuple[str, ...]] = set()

    def add(args: tuple[str, ...]) -> None:
        if len(args) == nargs and args not in seen:
            seen.add(args)
            tuples.append(args)

    if nargs == 1:
        for a in primary_terms:
            add((a,))
    else:
        for fill in relevant_vars:
            for a in primary_terms:
                for b in secondary_terms:
                    args = [fill] * nargs
                    args[0] = a
                    args[1] = b
                    add(tuple(args))
                    if len(tuples) >= limit:
                        break
                if len(tuples) >= limit:
                    break
            if len(tuples) >= limit:
                break

    for args in solver_core.instantiation_pool(h_eq, g_eq, max_terms=10):
        add(args)
        if len(tuples) >= limit:
            break

    return tuples[:limit]


def candidate_h_facts(h_eq: dict[str, Any], g_eq: dict[str, Any], limit: int) -> list[str]:
    lines = []
    for i, args in enumerate(candidate_h_args(h_eq, g_eq, limit), 1):
        lhs, rhs = render_h_type(h_eq, args)
        call = "h " + " ".join(args)
        lines.append(f"  f{i}: `have f{i} := {call}` gives `{lhs} = {rhs}`")
    return lines


def _dedupe_args(args_list: list[tuple[str, ...]]) -> list[tuple[str, ...]]:
    out: list[tuple[str, ...]] = []
    seen: set[tuple[str, ...]] = set()
    for args in args_list:
        if args not in seen:
            seen.add(args)
            out.append(args)
    return out


def candidate_lemma_args(
    lemma_eq: dict[str, Any],
    g_eq: dict[str, Any],
    limit: int,
    *,
    extra_args: list[tuple[str, ...]] | None = None,
) -> list[tuple[str, ...]]:
    nargs = len(lemma_eq["variables"])
    if nargs <= 0 or limit <= 0:
        return []
    pool = _unique(
        solver_core.goal_term_pool(g_eq, max_terms=12)
        + _small_goal_compounds(g_eq, limit=12)
        + g_eq["variables"]
    )
    rows: list[tuple[str, ...]] = []
    for combo in itertools.product(pool, repeat=nargs):
        rows.append(combo)
        if len(rows) >= limit:
            break
    return _dedupe_args((extra_args or []) + rows)[:limit]


def render_lemma_type(lemma_eq: dict[str, Any], args: tuple[str, ...]) -> tuple[str, str]:
    var_map = {
        var: args[i]
        for i, var in enumerate(lemma_eq["variables"])
    }
    return (
        solver_core.term_to_str_subst(lemma_eq["lhs"], var_map),
        solver_core.term_to_str_subst(lemma_eq["rhs"], var_map),
    )


def lemma_statement(lemma_eq: dict[str, Any]) -> str:
    lhs = solver_core.term_to_str(lemma_eq["lhs"])
    rhs = solver_core.term_to_str(lemma_eq["rhs"])
    if not lemma_eq["variables"]:
        return f"{lhs} = {rhs}"
    binders = " ".join(lemma_eq["variables"])
    return f"∀ {binders} : G, {lhs} = {rhs}"


def standard_lemma_kind(lemma_eq: dict[str, Any]) -> str | None:
    candidate = (lemma_eq["lhs"], lemma_eq["rhs"])
    for kind in ("const", "proj_l", "proj_r", "rowconst"):
        try:
            if solver_core._lemma_target(kind)(candidate):
                return kind
        except Exception:  # noqa: BLE001
            continue
    return None


def _special_rowconst_h_vars(h_eq: dict[str, Any]) -> tuple[str, str, str] | None:
    """Match H of the form x◇y = y◇(z◇(y◇z)), up to variable names."""
    lhs = h_eq["lhs"]
    rhs = h_eq["rhs"]
    if lhs[0] != "op" or rhs[0] != "op":
        return None
    if lhs[1][0] != "var" or lhs[2][0] != "var" or rhs[1][0] != "var":
        return None
    x_var = lhs[1][1]
    y_var = lhs[2][1]
    if rhs[1][1] != y_var:
        return None
    inner = rhs[2]
    if inner[0] != "op" or inner[1][0] != "var" or inner[2][0] != "op":
        return None
    z_var = inner[1][1]
    yz = inner[2]
    if yz[1] != ("var", y_var) or yz[2] != ("var", z_var):
        return None
    if len({x_var, y_var, z_var}) != 3:
        return None
    return x_var, y_var, z_var


def special_rowconst_body(h_eq: dict[str, Any], g_eq: dict[str, Any]) -> str | None:
    """Explicit no-grind proof for x◇y = y◇(z◇(y◇z)) rowconst cases."""
    matched = _special_rowconst_h_vars(h_eq)
    if matched is None:
        return None
    x_var, y_var, z_var = matched

    def h_call(x_arg: str, y_arg: str, z_arg: str) -> str:
        mapping = {x_var: x_arg, y_var: y_arg, z_var: z_arg}
        return "h " + " ".join(mapping[var] for var in h_eq["variables"])

    lhs = g_eq["lhs"]
    rhs = g_eq["rhs"]
    if lhs[0] != "op" or rhs[0] != "op":
        return None
    lhs_l = solver_core.term_to_str(lhs[1])
    lhs_r = solver_core.term_to_str(lhs[2])
    rhs_l = solver_core.term_to_str(rhs[1])
    rhs_r = solver_core.term_to_str(rhs[2])
    lhs_s = solver_core.term_to_str(lhs)
    rhs_s = solver_core.term_to_str(rhs)
    intro = "intro " + " ".join(g_eq["variables"]) if g_eq["variables"] else ""
    lines = []
    if intro:
        lines.append(intro)
    lines.extend([
        "have col : ∀ p q r : G, p ◇ q = r ◇ q := by",
        "  intro p q r",
        "  calc",
        f"    p ◇ q = q ◇ (q ◇ (q ◇ q)) := {h_call('p', 'q', 'q')}",
        f"    _ = r ◇ q := ({h_call('r', 'q', 'q')}).symm",
        "have rowconst : ∀ a b c : G, a ◇ b = a ◇ c := by",
        "  intro a b c",
        "  have hbcc : b ◇ c = c ◇ c := col b c c",
        "  calc",
        f"    a ◇ b = b ◇ (c ◇ (b ◇ c)) := {h_call('a', 'b', 'c')}",
        "    _ = c ◇ (c ◇ (b ◇ c)) := col b (c ◇ (b ◇ c)) c",
        "    _ = c ◇ (c ◇ (c ◇ c)) := by",
        "      exact congrArg (fun u => c ◇ (c ◇ u)) hbcc",
        f"    _ = a ◇ c := ({h_call('a', 'c', 'c')}).symm",
        "calc",
        f"  {lhs_s} = {rhs_l} ◇ {lhs_r} := col {lhs_l} {lhs_r} {rhs_l}",
        f"  _ = {rhs_s} := rowconst {rhs_l} {lhs_r} {rhs_r}",
    ])
    return "\n".join(lines)


def _special_square_rowconst_h_vars(h_eq: dict[str, Any]) -> tuple[str, str, str] | None:
    """Match H of the form x = (x◇x)◇((y◇z)◇z), up to variable names."""
    lhs = h_eq["lhs"]
    rhs = h_eq["rhs"]
    if lhs[0] != "var" or rhs[0] != "op":
        return None
    x_var = lhs[1]
    left = rhs[1]
    right = rhs[2]
    if left != ("op", ("var", x_var), ("var", x_var)):
        return None
    if right[0] != "op" or right[2][0] != "var":
        return None
    yz = right[1]
    z_var = right[2][1]
    if yz[0] != "op" or yz[1][0] != "var" or yz[2] != ("var", z_var):
        return None
    y_var = yz[1][1]
    if len({x_var, y_var, z_var}) != 3:
        return None
    return x_var, y_var, z_var


def special_square_rowconst_body(h_eq: dict[str, Any], g_eq: dict[str, Any]) -> str | None:
    """Explicit no-grind proof for x=(x◇x)◇((y◇z)◇z) rowconst-like goals."""
    matched = _special_square_rowconst_h_vars(h_eq)
    if matched is None:
        return None
    x_var, y_var, z_var = matched

    lhs = g_eq["lhs"]
    rhs = g_eq["rhs"]
    if lhs[0] != "var" or rhs[0] != "op":
        return None
    goal_x = solver_core.term_to_str(lhs)
    expected_left = ("op", lhs, lhs)
    if rhs[1] != expected_left:
        return None
    rhs_inner = solver_core.term_to_str(rhs[2])
    rhs_s = solver_core.term_to_str(rhs)
    xx = f"({goal_x} ◇ {goal_x})"
    xxx = f"(({goal_x} ◇ {goal_x}) ◇ {goal_x})"

    def h_call(x_arg: str, y_arg: str, z_arg: str) -> str:
        mapping = {x_var: x_arg, y_var: y_arg, z_var: z_arg}
        return "h " + " ".join(mapping[var] for var in h_eq["variables"])

    intro = "intro " + " ".join(g_eq["variables"]) if g_eq["variables"] else ""
    lines = []
    if intro:
        lines.append(intro)
    lines.extend([
        "have E1 : ∀ v0 v1 v2 v3 : G, (v0 ◇ v0) ◇ (v1 ◇ ((v2 ◇ v3) ◇ v3)) = v0 := by",
        "  intro v0 v1 v2 v3",
        f"  have ia := {h_call('v0', '(v1 ◇ v1)', '((v2 ◇ v3) ◇ v3)')}",
        f"  have ib := {h_call('v1', 'v2', 'v3')}",
        "  calc",
        "    (v0 ◇ v0) ◇ (v1 ◇ ((v2 ◇ v3) ◇ v3)) = (v0 ◇ v0) ◇ (((v1 ◇ v1) ◇ ((v2 ◇ v3) ◇ v3)) ◇ ((v2 ◇ v3) ◇ v3)) := by",
        "      exact congrArg (fun u => (v0 ◇ v0) ◇ (u ◇ ((v2 ◇ v3) ◇ v3))) ib",
        "    _ = v0 := ia.symm",
        "have E3 : ∀ v0 v1 v2 v3 : G, (v0 ◇ v0) ◇ v1 = v0 := by",
        "  intro v0 v1 v2 v3",
        "  have ia := E1 v0 (v1 ◇ v1) v2 v3",
        f"  have ib := {h_call('v1', 'v2', 'v3')}",
        "  calc",
        "    (v0 ◇ v0) ◇ v1 = (v0 ◇ v0) ◇ ((v1 ◇ v1) ◇ ((v2 ◇ v3) ◇ v3)) := by",
        "      exact congrArg (fun u => (v0 ◇ v0) ◇ u) ib",
        "    _ = v0 := ia",
        "have target : ∀ a b : G, a ◇ b = a ◇ a := by",
        "  intro a b",
        "  have ia := E3 (a ◇ a) b a a",
        "  have ib := E3 a (a ◇ a) a a",
        "  have bridge : ((a ◇ a) ◇ (a ◇ a)) ◇ b = a ◇ b := by",
        "    exact congrArg (fun u => u ◇ b) ib",
        "  exact bridge.symm.trans ia",
        "calc",
        f"  {goal_x} = {xx} ◇ {xxx} := {h_call(goal_x, goal_x, goal_x)}",
        f"  _ = {xx} ◇ {xx} := target {xx} {xxx}",
        f"  _ = {rhs_s} := (target {xx} {rhs_inner}).symm",
    ])
    return "\n".join(lines)


def _special_right_square_absorb_h_vars(h_eq: dict[str, Any]) -> tuple[str, str, str] | None:
    """Match H of the form x = (y◇(y◇z))◇(x◇x), up to variable names."""
    lhs = h_eq["lhs"]
    rhs = h_eq["rhs"]
    if lhs[0] != "var" or rhs[0] != "op":
        return None
    x_var = lhs[1]
    left = rhs[1]
    right = rhs[2]
    if right != ("op", ("var", x_var), ("var", x_var)):
        return None
    if left[0] != "op" or left[1][0] != "var" or left[2][0] != "op":
        return None
    y_var = left[1][1]
    yz = left[2]
    if yz[1] != ("var", y_var) or yz[2][0] != "var":
        return None
    z_var = yz[2][1]
    if len({x_var, y_var, z_var}) != 3:
        return None
    return x_var, y_var, z_var


def _special_right_square_absorb_goal_terms(g_eq: dict[str, Any]) -> tuple[str, str] | None:
    """Match goals a = a◇((b◇(a◇b))◇a), up to variable names."""
    lhs = g_eq["lhs"]
    rhs = g_eq["rhs"]
    if lhs[0] != "var" or rhs[0] != "op" or rhs[1] != lhs:
        return None
    inner = rhs[2]
    if inner[0] != "op" or inner[2] != lhs:
        return None
    left = inner[1]
    if left[0] != "op":
        return None
    b_term = left[1]
    ab_term = left[2]
    if ab_term != ("op", lhs, b_term):
        return None
    return solver_core.term_to_str(lhs), solver_core.term_to_str(b_term)


def _right_square_absorb_helper_lines(
    h_eq: dict[str, Any],
    *,
    square_absorb_name: str = "square_absorb",
    right_square_name: str = "right_square",
) -> list[str] | None:
    """Explicit helpers for x=(y◇(y◇z))◇(x◇x) families.

    The returned helpers have the two-argument statements expected by the
    generic lemma-chain graph consumer.
    """
    matched = _special_right_square_absorb_h_vars(h_eq)
    if matched is None:
        return None
    h_x, h_y, h_z = matched

    def h_call(x_arg: str, y_arg: str, z_arg: str) -> str:
        mapping = {h_x: x_arg, h_y: y_arg, h_z: z_arg}
        return "h " + " ".join(mapping[var] for var in h_eq["variables"])

    return [
        "have E4 : ∀ (v0 v1 v2 v3 v4 : G), ((v0 ◇ (v0 ◇ v1)) ◇ ((v2 ◇ (v2 ◇ v3)) ◇ ((v4 ◇ v4) ◇ (v4 ◇ v4)))) = v4 := by",
        "  intro v0 v1 v2 v3 v4",
        f"  have ia : v4 = ((v0 ◇ (v0 ◇ v1)) ◇ (v4 ◇ v4)) := {h_call('v4', 'v0', 'v1')}",
        f"  have ib : (v4 ◇ v4) = ((v2 ◇ (v2 ◇ v3)) ◇ ((v4 ◇ v4) ◇ (v4 ◇ v4))) := {h_call('(v4 ◇ v4)', 'v2', 'v3')}",
        "  have ic : ((v0 ◇ (v0 ◇ v1)) ◇ (v4 ◇ v4)) = ((v0 ◇ (v0 ◇ v1)) ◇ ((v2 ◇ (v2 ◇ v3)) ◇ ((v4 ◇ v4) ◇ (v4 ◇ v4)))) := congrArg (fun t => ((v0 ◇ (v0 ◇ v1)) ◇ t)) ib",
        "  exact (ia.trans ic).symm",
        "have raw_square_absorb : ∀ (v0 v1 v2 v3 : G), (v0 ◇ (v1 ◇ v1)) = v1 := by",
        "  intro v0 v1 v2 v3",
        f"  have ia : v1 = (((v2 ◇ (v2 ◇ v3)) ◇ ((v2 ◇ (v2 ◇ v3)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0)))) ◇ (v1 ◇ v1)) := {h_call('v1', '((v2 ◇ (v2 ◇ v3)))', '(((v0 ◇ v0) ◇ (v0 ◇ v0)))')}",
        "  have ib : ((v2 ◇ (v2 ◇ v3)) ◇ ((v2 ◇ (v2 ◇ v3)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0)))) = v0 := E4 v2 v3 v2 v3 v0",
        "  have ic : (((v2 ◇ (v2 ◇ v3)) ◇ ((v2 ◇ (v2 ◇ v3)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0)))) ◇ (v1 ◇ v1)) = (v0 ◇ (v1 ◇ v1)) := congrArg (fun t => t ◇ (v1 ◇ v1)) ib",
        "  exact (ia.trans ic).symm",
        f"have {square_absorb_name} : ∀ (v0 v1 : G), (v0 ◇ (v1 ◇ v1)) = v1 := by",
        "  intro v0 v1",
        "  exact raw_square_absorb v0 v1 v0 v0",
        "have raw_right_square : ∀ (v0 v1 v2 v3 v4 v5 : G), (v0 ◇ v1) = (v1 ◇ v1) := by",
        "  intro v0 v1 v2 v3 v4 v5",
        f"  have ia : v0 ◇ ((v1 ◇ v1) ◇ (v1 ◇ v1)) = (v1 ◇ v1) := {square_absorb_name} v0 (v1 ◇ v1)",
        f"  have ib : ((v1 ◇ v1) ◇ (v1 ◇ v1)) = v1 := {square_absorb_name} (v1 ◇ v1) v1",
        "  have ic : v0 ◇ ((v1 ◇ v1) ◇ (v1 ◇ v1)) = v0 ◇ v1 := congrArg (fun t => v0 ◇ t) ib",
        "  exact ic.symm.trans ia",
        f"have {right_square_name} : ∀ (v0 v1 : G), (v0 ◇ v1) = (v1 ◇ v1) := by",
        "  intro v0 v1",
        "  exact raw_right_square v0 v1 v0 v0 v0 v0",
    ]


def special_right_square_absorb_body(h_eq: dict[str, Any], g_eq: dict[str, Any]) -> str | None:
    """Explicit no-grind proof for x=(y◇(y◇z))◇(x◇x) absorption goals."""
    goal_terms = _special_right_square_absorb_goal_terms(g_eq)
    helper_lines = _right_square_absorb_helper_lines(h_eq)
    if helper_lines is None or goal_terms is None:
        return None
    goal_x, goal_y = goal_terms

    xy = f"({goal_x} ◇ {goal_y})"
    yxy = f"({goal_y} ◇ {xy})"
    target_inner = f"({yxy} ◇ {goal_x})"
    intro = "intro " + " ".join(g_eq["variables"]) if g_eq["variables"] else ""
    lines: list[str] = []
    if intro:
        lines.append(intro)
    lines.extend(helper_lines)
    lines.extend([
        f"have t1 : {yxy} = ({xy} ◇ {xy}) := right_square {goal_y} {xy}",
        f"have t2 : {target_inner} = ({goal_x} ◇ {goal_x}) := by",
        f"  have a : {target_inner} = (({xy} ◇ {xy}) ◇ {goal_x}) := congrArg (fun t => t ◇ {goal_x}) t1",
        f"  have b : (({xy} ◇ {xy}) ◇ {goal_x}) = ({goal_x} ◇ {goal_x}) := right_square ({xy} ◇ {xy}) {goal_x}",
        "  exact a.trans b",
        f"have t3 : {goal_x} ◇ {target_inner} = {goal_x} ◇ ({goal_x} ◇ {goal_x}) := congrArg (fun u => {goal_x} ◇ u) t2",
        f"have t4 : {goal_x} ◇ ({goal_x} ◇ {goal_x}) = {goal_x} := square_absorb {goal_x} {goal_x}",
        "exact (t3.trans t4).symm",
    ])
    return "\n".join(lines)


def _special_square_sandwich_h_vars(h_eq: dict[str, Any]) -> tuple[str, str, str] | None:
    """Match H of the form x = ((y◇x)◇y)◇(z◇z), up to variable names."""
    lhs = h_eq["lhs"]
    rhs = h_eq["rhs"]
    if lhs[0] != "var" or rhs[0] != "op":
        return None
    x_var = lhs[1]
    sandwich_part = rhs[1]
    square_part = rhs[2]
    if sandwich_part[0] != "op" or square_part[0] != "op":
        return None
    yx = sandwich_part[1]
    y_rhs = sandwich_part[2]
    if yx[0] != "op" or y_rhs[0] != "var":
        return None
    y_left = yx[1]
    x_inner = yx[2]
    if y_left[0] != "var" or x_inner != ("var", x_var):
        return None
    y_var = y_left[1]
    if y_rhs[1] != y_var:
        return None
    if square_part[1][0] != "var" or square_part[2] != square_part[1]:
        return None
    z_var = square_part[1][1]
    if len({x_var, y_var, z_var}) != 3:
        return None
    return x_var, y_var, z_var


def _lean_arg(text: str) -> str:
    text = text.strip()
    if ("◇" in text or " " in text) and not (text.startswith("(") and text.endswith(")")):
        return f"({text})"
    return text


def _term_op(left: Any, right: Any) -> tuple[Any, Any, Any]:
    return ("op", left, right)


def _term_square(term: Any) -> tuple[Any, Any, Any]:
    return ("op", term, term)


def _is_square(term: Any) -> Any | None:
    if term[0] == "op" and term[1] == term[2]:
        return term[1]
    return None


def _square_sandwich_lemma_kind(lemma_eq: dict[str, Any]) -> str | None:
    def classify(lhs: Any, rhs: Any) -> str | None:
        if lhs[0] == "op" and rhs[0] == "op":
            l_sq = _is_square(lhs)
            r_sq = _is_square(rhs)
            if l_sq is not None and r_sq is not None and l_sq != r_sq:
                return "square_const"
        if lhs[0] == "op" and rhs[0] == "var":
            left = lhs[1]
            right = lhs[2]
            if right[0] == "op" and right[1] == right[2] and left == rhs:
                return "right_id_square"
            if left[0] == "op" and left[2] == rhs and left[1] == right:
                return "sandwich"
            if right[0] == "op" and right[1] == rhs and right[2] == left:
                return "left_sandwich"
        return None

    return (
        classify(lemma_eq["lhs"], lemma_eq["rhs"])
        or classify(lemma_eq["rhs"], lemma_eq["lhs"])
    )


RIGHT_SQUARE_HELPER_EQUATIONS = {
    "square_absorb": "u ◇ (v ◇ v) = v",
    "right_square": "u ◇ v = v ◇ v",
}


def _right_square_lemma_kind(lemma_eq: dict[str, Any]) -> str | None:
    def classify(lhs: Any, rhs: Any) -> str | None:
        if lhs[0] != "op":
            return None
        if rhs[0] == "var":
            right = lhs[2]
            if right == ("op", rhs, rhs):
                return "square_absorb"
        if rhs[0] == "op" and rhs[1] == rhs[2] and lhs[2] == rhs[1]:
            return "right_square"
        return None

    return (
        classify(lemma_eq["lhs"], lemma_eq["rhs"])
        or classify(lemma_eq["rhs"], lemma_eq["lhs"])
    )


def _lemma_chain_helper_kind(lemma_eq: dict[str, Any]) -> str | None:
    return _square_sandwich_lemma_kind(lemma_eq) or _right_square_lemma_kind(lemma_eq)


def _canonical_helper_eq(kind: str, lemma_eq: dict[str, Any]) -> dict[str, Any]:
    equation = RIGHT_SQUARE_HELPER_EQUATIONS.get(kind)
    if equation is None:
        return lemma_eq
    return solver_core.parse_equation(solver_core.normalize(equation))


def _square_sandwich_chain_advice(h_eq: dict[str, Any], mode: str) -> str:
    if mode not in ("lemma_hint", "lemma_chain"):
        return ""
    if _special_square_sandwich_h_vars(h_eq) is None:
        return ""
    return (
        "Machine-readable square-witness chain advice:\n"
        + json.dumps({
            "candidate_chain": [
                "u ◇ u = v ◇ v",
                "u ◇ (v ◇ v) = u",
                "(v ◇ u) ◇ v = u",
                "v ◇ (u ◇ v) = u",
            ],
            "reason": (
                "H has the x = ((y ◇ x) ◇ y) ◇ (z ◇ z) shape; a witness-square "
                "chain can let the mechanical side close compatible goals."
            ),
        }, ensure_ascii=False, indent=2)
        + "\n\n"
    )


def _square_sandwich_helper_lines(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
) -> list[str] | None:
    matched = _special_square_sandwich_h_vars(h_eq)
    if matched is None or not g_eq["variables"]:
        return None
    x_var, y_var, z_var = matched

    def h_call(x_arg: str, y_arg: str, z_arg: str) -> str:
        mapping = {x_var: x_arg, y_var: y_arg, z_var: z_arg}
        return "h " + " ".join(_lean_arg(mapping[var]) for var in h_eq["variables"])

    intro = "intro " + " ".join(g_eq["variables"])
    return [
        intro,
        "have square_const : ∀ v w : G, v ◇ v = w ◇ w := by",
        "  intro v w",
        "  let A : G := (v ◇ (v ◇ v)) ◇ v",
        "  have hvA : v ◇ v = A ◇ (v ◇ v) := by",
        f"    simpa [A] using {h_call('v ◇ v', 'v', 'v')}",
        "  have hwA : v ◇ v = A ◇ (w ◇ w) := by",
        f"    simpa [A] using {h_call('v ◇ v', 'v', 'w')}",
        "  have ev : v ◇ v = ((v ◇ v) ◇ A) ◇ (v ◇ v) := by",
        "    calc",
        f"      v ◇ v = ((A ◇ (v ◇ v)) ◇ A) ◇ (v ◇ v) := {h_call('v ◇ v', 'A', 'v')}",
        "      _ = ((v ◇ v) ◇ A) ◇ (v ◇ v) := by rw [← hvA]",
        "  have ew : w ◇ w = ((v ◇ v) ◇ A) ◇ (v ◇ v) := by",
        "    calc",
        f"      w ◇ w = ((A ◇ (w ◇ w)) ◇ A) ◇ (v ◇ v) := {h_call('w ◇ w', 'A', 'v')}",
        "      _ = ((v ◇ v) ◇ A) ◇ (v ◇ v) := by rw [← hwA]",
        "  exact ev.trans ew.symm",
        "have right_id_square : ∀ a b : G, a ◇ (b ◇ b) = a := by",
        "  intro a b",
        "  have sq : a ◇ a = b ◇ b := square_const a b",
        "  have step1 : ((b ◇ b) ◇ a) ◇ (b ◇ b) = a := by",
        "    calc",
        "      ((b ◇ b) ◇ a) ◇ (b ◇ b) = ((a ◇ a) ◇ a) ◇ (b ◇ b) := by rw [← sq]",
        f"      _ = a := ({h_call('a', 'a', 'b')}).symm",
        "  have step2 : a = a ◇ (b ◇ b) := by",
        "    calc",
        f"      a = (((b ◇ b) ◇ a) ◇ (b ◇ b)) ◇ (b ◇ b) := {h_call('a', 'b ◇ b', 'b')}",
        "      _ = a ◇ (b ◇ b) := by rw [step1]",
        "  exact step2.symm",
        "have sandwich : ∀ a b : G, (b ◇ a) ◇ b = a := by",
        "  intro a b",
        "  calc",
        "    (b ◇ a) ◇ b = ((b ◇ a) ◇ b) ◇ (a ◇ a) := (right_id_square ((b ◇ a) ◇ b) a).symm",
        f"    _ = a := ({h_call('a', 'b', 'a')}).symm",
        "have left_sandwich : ∀ a b : G, b ◇ (a ◇ b) = a := by",
        "  intro a b",
        "  have d_eq_a : (((a ◇ b) ◇ a) ◇ (a ◇ b)) = a := by",
        "    calc",
        "      (((a ◇ b) ◇ a) ◇ (a ◇ b)) = (((a ◇ b) ◇ a) ◇ (a ◇ b)) ◇ (a ◇ a) := (right_id_square (((a ◇ b) ◇ a) ◇ (a ◇ b)) a).symm",
        f"      _ = a := ({h_call('a', 'a ◇ b', 'a')}).symm",
        "  calc",
        "    b ◇ (a ◇ b) = (((a ◇ b) ◇ a) ◇ (a ◇ b)) := congrArg (fun u => u ◇ (a ◇ b)) (sandwich b a).symm",
        "    _ = a := d_eq_a",
    ]


class _SquareSandwichReducer:
    def __init__(self, witness_var: str):
        self.witness_var = witness_var
        self.witness = _term_square(("var", witness_var))
        self.lines: list[str] = []
        self.counter = 0

    def fresh(self) -> str:
        self.counter += 1
        return f"sq_chain_{self.counter}"

    def term(self, t: Any) -> str:
        return solver_core.term_to_str(t)

    def add_calc(self, name: str, start: Any, steps: list[tuple[Any, str]]) -> None:
        end = steps[-1][0]
        self.lines.append(f"have {name} : {self.term(start)} = {self.term(end)} := by")
        if len(steps) == 1:
            self.lines.append(f"  exact {steps[0][1]}")
            return
        self.lines.append("  calc")
        for idx, (to_term, proof_expr) in enumerate(steps):
            from_text = self.term(start) if idx == 0 else "_"
            self.lines.append(f"    {from_text} = {self.term(to_term)} := {proof_expr}")

    def root_steps(self, term: Any) -> tuple[Any, list[tuple[Any, str]]]:
        current = term
        steps: list[tuple[Any, str]] = []
        while current[0] == "op":
            left = current[1]
            right = current[2]
            if right[0] == "op" and right[1] == right[2]:
                next_term = left
                steps.append((next_term, f"right_id_square {self.term(left)} {self.term(right[1])}"))
                current = next_term
                continue
            if left[0] == "op" and left[1] == right:
                next_term = left[2]
                steps.append((next_term, f"sandwich {self.term(left[2])} {self.term(right)}"))
                current = next_term
                continue
            if right[0] == "op" and right[2] == left:
                next_term = right[1]
                steps.append((next_term, f"left_sandwich {self.term(right[1])} {self.term(left)}"))
                current = next_term
                continue
            square_base = _is_square(current)
            if square_base is not None and current != self.witness:
                next_term = self.witness
                steps.append((next_term, f"square_const {self.term(square_base)} {self.witness_var}"))
                current = next_term
                continue
            break
        return current, steps

    def reduce(self, term: Any) -> tuple[Any, str | None]:
        if term[0] == "var":
            return term, None

        left = term[1]
        right = term[2]
        left_norm, left_proof = self.reduce(left)
        right_norm, right_proof = self.reduce(right)

        current = _term_op(left_norm, right_norm)
        steps: list[tuple[Any, str]] = []
        if left_proof is not None:
            mid = _term_op(left_norm, right)
            steps.append((mid, f"congrArg (fun u => u ◇ {self.term(right)}) {left_proof}"))
        if right_proof is not None:
            mid = _term_op(left_norm, right_norm)
            steps.append((mid, f"congrArg (fun u => {self.term(left_norm)} ◇ u) {right_proof}"))

        final, root_steps = self.root_steps(current)
        steps.extend(root_steps)

        if not steps:
            return term, None
        name = self.fresh()
        self.add_calc(name, term, steps)
        return final, name


def special_square_sandwich_chain_body(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
) -> tuple[str | None, dict[str, Any]]:
    helper_lines = _square_sandwich_helper_lines(h_eq, g_eq)
    if helper_lines is None:
        return None, {
            "kind": "square_sandwich_chain",
            "status": "not_applicable",
            "reason": "H is not x = ((y ◇ x) ◇ y) ◇ (z ◇ z), or the goal has no variables.",
        }

    reducer = _SquareSandwichReducer(g_eq["variables"][0])
    lhs_norm, lhs_proof = reducer.reduce(g_eq["lhs"])
    rhs_norm, rhs_proof = reducer.reduce(g_eq["rhs"])
    lhs_text = solver_core.term_to_str(lhs_norm)
    rhs_text = solver_core.term_to_str(rhs_norm)
    if lhs_norm != rhs_norm:
        return None, {
            "kind": "square_sandwich_chain",
            "status": "goal_not_closed",
            "lhs_normal_form": lhs_text,
            "rhs_normal_form": rhs_text,
            "reason": (
                "The square-constant/right-identity/sandwich simplifier did not "
                "reduce the two sides to the same term."
            ),
        }

    lines = list(helper_lines)
    lines.extend(reducer.lines)
    if lhs_proof is None and rhs_proof is None:
        lines.append("rfl")
    elif lhs_proof is None:
        lines.append(f"exact {rhs_proof}.symm")
    elif rhs_proof is None:
        lines.append(f"exact {lhs_proof}")
    else:
        lines.append(f"exact {lhs_proof}.trans {rhs_proof}.symm")

    return "\n".join(lines), {
        "kind": "square_sandwich_chain",
        "status": "body_built",
        "lhs_normal_form": lhs_text,
        "rhs_normal_form": rhs_text,
        "helper_lemmas": ["square_const", "right_id_square", "sandwich", "left_sandwich"],
    }


def indent_lean(body: str, spaces: int = 2) -> str:
    prefix = " " * spaces
    return "\n".join(prefix + line if line.strip() else line for line in body.splitlines())


def _fact_have_line(fact: dict[str, Any]) -> str:
    if fact["kind"] == "base":
        return f"have {fact['name']} := {fact['call']}"
    return f"have {fact['name']} : {fact['lhs']} = {fact['rhs']} := {fact['proof']}"


def _fact_calc_proof(fact: dict[str, Any], reversed_edge: bool) -> str:
    suffix = ".symm" if reversed_edge else ""
    return f"by simpa using {fact['name']}{suffix}"


def _fact_dependencies(facts_by_name: dict[str, dict[str, Any]], fact: dict[str, Any]) -> list[dict[str, Any]]:
    ordered: list[dict[str, Any]] = []
    seen: set[str] = set()

    def visit(name: str) -> None:
        if name in seen:
            return
        seen.add(name)
        item = facts_by_name[name]
        for dep in item.get("deps", []):
            visit(dep)
        ordered.append(item)

    visit(fact["name"])
    return ordered


def _context_terms_from_goal_and_facts(
    g_eq: dict[str, Any],
    facts: list[dict[str, Any]],
    *,
    limit: int,
) -> list[str]:
    terms = (
        solver_core.goal_term_pool(g_eq, max_terms=limit)
        + _small_goal_compounds(g_eq, limit=limit)
        + g_eq["variables"]
    )
    for fact in facts[: max(4, limit)]:
        for side in (fact["lhs"], fact["rhs"]):
            for var in re.findall(r"\b([a-z])\b", side):
                terms.append(var)
    return _unique(terms)[:limit]


def _build_graph_facts(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    limit: int,
    *,
    extra_args: list[tuple[str, ...]] | None = None,
    lemmas: list[dict[str, Any]] | None = None,
    lemma_fact_limit: int = 96,
    congruence_depth: int = 0,
    max_congruence_facts: int = 240,
) -> list[dict[str, Any]]:
    facts: list[dict[str, Any]] = []
    seen_edges: set[tuple[str, str]] = set()

    def add_fact(fact: dict[str, Any]) -> bool:
        edge = (fact["lhs"], fact["rhs"])
        if edge in seen_edges or (edge[1], edge[0]) in seen_edges:
            return False
        seen_edges.add(edge)
        facts.append(fact)
        return True

    all_args = _dedupe_args((extra_args or []) + candidate_h_args(h_eq, g_eq, limit))
    for args in all_args:
        lhs, rhs = render_h_type(h_eq, args)
        add_fact({
            "name": f"f{len(facts) + 1}",
            "kind": "base",
            "source": "h",
            "call": "h " + " ".join(args),
            "lhs": lhs,
            "rhs": rhs,
            "deps": [],
        })

    for lemma in lemmas or []:
        lemma_eq = lemma["eq"]
        lemma_name = lemma.get("name", "mid")
        lemma_args = candidate_lemma_args(
            lemma_eq,
            g_eq,
            lemma_fact_limit,
            extra_args=lemma.get("extra_args") or [],
        )
        for args in lemma_args:
            lhs, rhs = render_lemma_type(lemma_eq, args)
            add_fact({
                "name": f"f{len(facts) + 1}",
                "kind": "base",
                "source": "lemma",
                "call": lemma_name + " " + " ".join(args),
                "lhs": lhs,
                "rhs": rhs,
                "deps": [],
            })

    if congruence_depth <= 0:
        return facts

    context_terms = _context_terms_from_goal_and_facts(g_eq, facts, limit=16)
    derivable = list(facts)
    made = 0
    for _depth in range(congruence_depth):
        snapshot = list(derivable)
        for fact in snapshot:
            for term in context_terms:
                if made >= max_congruence_facts:
                    return facts
                if term in (fact["lhs"], fact["rhs"]):
                    continue
                left_lhs = f"({fact['lhs']} ◇ {term})"
                left_rhs = f"({fact['rhs']} ◇ {term})"
                added = add_fact({
                    "name": f"f{len(facts) + 1}",
                    "kind": "congruence",
                    "source": "congr_left",
                    "lhs": left_lhs,
                    "rhs": left_rhs,
                    "deps": [fact["name"]],
                    "proof": f"by simpa using congrArg (fun u => u ◇ {term}) {fact['name']}",
                })
                if added:
                    derivable.append(facts[-1])
                    made += 1
                if made >= max_congruence_facts:
                    return facts
                right_lhs = f"({term} ◇ {fact['lhs']})"
                right_rhs = f"({term} ◇ {fact['rhs']})"
                added = add_fact({
                    "name": f"f{len(facts) + 1}",
                    "kind": "congruence",
                    "source": "congr_right",
                    "lhs": right_lhs,
                    "rhs": right_rhs,
                    "deps": [fact["name"]],
                    "proof": f"by simpa using congrArg (fun u => {term} ◇ u) {fact['name']}",
                })
                if added:
                    derivable.append(facts[-1])
                    made += 1
    return facts


def h_graph_body(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    limit: int,
    *,
    extra_args: list[tuple[str, ...]] | None = None,
    lemmas: list[dict[str, Any]] | None = None,
    lemma_fact_limit: int = 96,
    congruence_depth: int = 0,
    max_congruence_facts: int = 240,
) -> str | None:
    """Try a pure equality-graph proof using generated h-instantiations."""
    facts = _build_graph_facts(
        h_eq,
        g_eq,
        limit,
        extra_args=extra_args,
        lemmas=lemmas,
        lemma_fact_limit=lemma_fact_limit,
        congruence_depth=congruence_depth,
        max_congruence_facts=max_congruence_facts,
    )
    facts_by_name = {fact["name"]: fact for fact in facts}

    start = solver_core.term_to_str(g_eq["lhs"])
    target = solver_core.term_to_str(g_eq["rhs"])
    adjacency: dict[str, list[tuple[str, dict[str, Any], bool]]] = {}
    for fact in facts:
        adjacency.setdefault(fact["lhs"], []).append((fact["rhs"], fact, False))
        adjacency.setdefault(fact["rhs"], []).append((fact["lhs"], fact, True))

    queue = [start]
    parent: dict[str, tuple[str, dict[str, Any], bool] | None] = {start: None}
    while queue and target not in parent:
        current = queue.pop(0)
        for nxt, fact, reversed_edge in adjacency.get(current, []):
            if nxt in parent:
                continue
            parent[nxt] = (current, fact, reversed_edge)
            queue.append(nxt)

    if target not in parent:
        return None

    path: list[tuple[str, str, dict[str, Any], bool]] = []
    node = target
    while parent[node] is not None:
        prev, fact, reversed_edge = parent[node]  # type: ignore[misc]
        path.append((prev, node, fact, reversed_edge))
        node = prev
    path.reverse()
    if not path:
        return "intro " + " ".join(g_eq["variables"]) + "\nrfl"

    used: list[dict[str, Any]] = []
    seen_names: set[str] = set()
    for _, _, fact, _ in path:
        for dep_fact in _fact_dependencies(facts_by_name, fact):
            if dep_fact["name"] not in seen_names:
                seen_names.add(dep_fact["name"])
                used.append(dep_fact)

    lines = ["intro " + " ".join(g_eq["variables"])]
    for fact in used:
        lines.append(_fact_have_line(fact))
    first_prev, first_next, first_fact, first_reversed = path[0]
    lines.append("calc")
    lines.append(f"  {first_prev} = {first_next} := {_fact_calc_proof(first_fact, first_reversed)}")
    for _, nxt, fact, reversed_edge in path[1:]:
        lines.append(f"  _ = {nxt} := {_fact_calc_proof(fact, reversed_edge)}")
    return "\n".join(lines)


def h_graph_diagnostics(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    limit: int,
    *,
    extra_args: list[tuple[str, ...]] | None = None,
    sample: int = 10,
) -> str:
    all_args = _dedupe_args((extra_args or []) + candidate_h_args(h_eq, g_eq, limit))
    adjacency: dict[str, set[str]] = {}
    for args in all_args:
        lhs, rhs = render_h_type(h_eq, args)
        adjacency.setdefault(lhs, set()).add(rhs)
        adjacency.setdefault(rhs, set()).add(lhs)

    def component(seed: str) -> set[str]:
        seen = {seed}
        queue = [seed]
        while queue:
            current = queue.pop(0)
            for nxt in adjacency.get(current, set()):
                if nxt not in seen:
                    seen.add(nxt)
                    queue.append(nxt)
        return seen

    def summarize(terms: set[str]) -> str:
        ordered = sorted(terms, key=lambda s: (len(s), s))[:sample]
        return "\n".join(f"  - {term}" for term in ordered)

    start = solver_core.term_to_str(g_eq["lhs"])
    target = solver_core.term_to_str(g_eq["rhs"])
    start_comp = component(start)
    target_comp = component(target)
    return (
        f"Graph component containing goal-left `{start}` has {len(start_comp)} terms:\n"
        f"{summarize(start_comp)}\n\n"
        f"Graph component containing goal-right `{target}` has {len(target_comp)} terms:\n"
        f"{summarize(target_comp)}"
    )


def build_search_state(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    limit: int,
    *,
    extra_args: list[tuple[str, ...]] | None = None,
    lemmas: list[dict[str, Any]] | None = None,
    lemma_fact_limit: int = 96,
    congruence_depth: int = 0,
    max_congruence_facts: int = 240,
    sample: int = 12,
    status: str | None = None,
    failed_hints: list[dict[str, Any]] | None = None,
    budget_used: dict[str, Any] | None = None,
) -> dict[str, Any]:
    facts = _build_graph_facts(
        h_eq,
        g_eq,
        limit,
        extra_args=extra_args,
        lemmas=lemmas,
        lemma_fact_limit=lemma_fact_limit,
        congruence_depth=congruence_depth,
        max_congruence_facts=max_congruence_facts,
    )
    adjacency: dict[str, set[str]] = {}
    for fact in facts:
        adjacency.setdefault(fact["lhs"], set()).add(fact["rhs"])
        adjacency.setdefault(fact["rhs"], set()).add(fact["lhs"])

    def component(seed: str) -> set[str]:
        seen = {seed}
        queue = [seed]
        while queue:
            current = queue.pop(0)
            for nxt in adjacency.get(current, set()):
                if nxt not in seen:
                    seen.add(nxt)
                    queue.append(nxt)
        return seen

    def summarize(terms: set[str]) -> list[str]:
        return sorted(terms, key=lambda s: (len(s), s))[:sample]

    def closest_pairs(left_terms: set[str], right_terms: set[str]) -> list[dict[str, Any]]:
        pairs: list[dict[str, Any]] = []
        for left in summarize(left_terms)[:sample]:
            for right in summarize(right_terms)[:sample]:
                score = round(difflib.SequenceMatcher(None, left, right).ratio(), 3)
                pairs.append({"left": left, "right": right, "similarity": score})
        return sorted(pairs, key=lambda p: -p["similarity"])[:6]

    start = solver_core.term_to_str(g_eq["lhs"])
    target = solver_core.term_to_str(g_eq["rhs"])
    left_comp = component(start)
    right_comp = component(target)
    connected = target in left_comp
    left_sample = summarize(left_comp)
    right_sample = summarize(right_comp)
    closest = [] if connected else closest_pairs(left_comp, right_comp)
    need_hint = None
    if closest:
        best = closest[0]
        need_hint = {
            "kind": "need_hint",
            "need_hint": "prove these two terms equal",
            "left_term": best["left"],
            "right_term": best["right"],
            "reason": (
                "This equality would connect the current goal-left and "
                "goal-right graph components."
            ),
            "similarity": best["similarity"],
        }
    by_kind: dict[str, int] = {}
    for fact in facts:
        by_kind[fact["kind"]] = by_kind.get(fact["kind"], 0) + 1
    proved_facts = [
        {
            "name": fact["name"],
            "kind": fact["kind"],
            "source": fact.get("source"),
            "lhs": fact["lhs"],
            "rhs": fact["rhs"],
        }
        for fact in facts[: min(24, len(facts))]
    ]
    proved_lemmas = [
        {
            "name": lemma.get("name", "mid"),
            "equation": lemma.get("eq", {}).get("text"),
            "extra_args": lemma.get("extra_args") or [],
        }
        for lemma in (lemmas or [])
    ]
    effective_budget = {
        "max_h_facts": limit,
        "max_lemma_facts": lemma_fact_limit,
        "congruence_depth": congruence_depth,
        "max_congruence_facts": max_congruence_facts,
    }
    if budget_used:
        effective_budget.update(budget_used)
    return {
        "kind": "search_state",
        "goal": g_eq["text"],
        "target": g_eq["text"],
        "status": status or ("connected" if connected else "stuck"),
        "proved_facts": proved_facts,
        "left_frontier": left_sample,
        "right_frontier": right_sample,
        "proved_lemmas": proved_lemmas,
        "failed_hints": failed_hints or [],
        "budget_used": effective_budget,
        "connected": connected,
        "graph": {
            "fact_count": len(facts),
            "facts_by_kind": by_kind,
            "congruence_depth": congruence_depth,
            "max_congruence_facts": max_congruence_facts,
        },
        "congruence": {
            "congruence_depth": congruence_depth,
            "terms_generated": len(adjacency),
            "left_component_size": len(left_comp),
            "right_component_size": len(right_comp),
            "closest_pairs": closest,
        },
        "left_component": {
            "term": start,
            "size": len(left_comp),
            "sample": left_sample,
        },
        "right_component": {
            "term": target,
            "size": len(right_comp),
            "sample": right_sample,
        },
        "closest_pairs": closest,
        "need_hint": need_hint,
        "missing_bridge": None if connected else {
            "wanted": "an h-instantiation, lemma, or lemma instance connecting the left and right components",
            "left_component_term": start,
            "right_component_term": target,
            "need_hint": need_hint,
        },
    }


def search_state_text(state: dict[str, Any], *, max_chars: int = 5000) -> str:
    text = json.dumps(state, ensure_ascii=False, indent=2)
    if len(text) > max_chars:
        return text[:max_chars] + "\n... (truncated)"
    return text


def _as_dict(value: Any) -> dict[str, Any]:
    return value if isinstance(value, dict) else {}


def _state_need_hint(*states: Any) -> dict[str, Any] | None:
    for state in states:
        if isinstance(state, dict):
            need_hint = state.get("need_hint")
            if isinstance(need_hint, dict):
                return need_hint
    return None


def collaboration_state_from_attempt(attempt: dict[str, Any]) -> dict[str, Any]:
    """Normalize true/false attempt diagnostics into one prompt-facing state."""
    if isinstance(attempt.get("collaboration_state"), dict):
        return attempt["collaboration_state"]

    result = _as_dict(attempt.get("result"))
    search_state = _as_dict(attempt.get("search_state") or result.get("search_state"))
    module_state = _as_dict(attempt.get("module_state") or result.get("module_state"))
    lifecycle = _as_dict(attempt.get("lemma_lifecycle") or result.get("lemma_lifecycle"))
    chain_state = _as_dict(result.get("chain_state") or result.get("chain_state"))
    if not chain_state and module_state.get("kind") == "square_sandwich_chain":
        chain_state = module_state

    llm_payload = _as_dict(attempt.get("llm_payload"))
    hint_summary: dict[str, Any] = {
        "kind": (
            llm_payload.get("kind")
            or ("false_model_hint" if attempt.get("false_model_hint") else None)
            or ("lemma_hint" if attempt.get("lemma_hint") else None)
            or ("lemma_chain" if attempt.get("lemma_chain") else None)
            or ("tool_call" if attempt.get("tool_call") else None)
            or ("h_args" if llm_payload.get("h_args") else None)
        )
    }
    for key in ("false_model_hint", "lemma_hint", "lemma_chain", "tool_call"):
        if isinstance(attempt.get(key), dict):
            hint_summary[key] = attempt[key]

    mechanical: dict[str, Any] = {}
    budgets: dict[str, Any] = {}
    proved_artifacts: list[dict[str, Any]] = []
    failed_hints: list[dict[str, Any]] = []

    if search_state:
        graph = _as_dict(search_state.get("graph"))
        congruence = _as_dict(search_state.get("congruence"))
        left_component = _as_dict(search_state.get("left_component"))
        right_component = _as_dict(search_state.get("right_component"))
        mechanical["graph"] = {
            "status": search_state.get("status"),
            "connected": search_state.get("connected"),
            "fact_count": graph.get("fact_count"),
            "left_component_size": left_component.get("size"),
            "right_component_size": right_component.get("size"),
            "closest_pairs": congruence.get("closest_pairs"),
        }
        budgets.update(_as_dict(search_state.get("budget_used")))
        for lemma in search_state.get("proved_lemmas") or []:
            if isinstance(lemma, dict):
                proved_artifacts.append({"kind": "lemma", **lemma})
        for failed in search_state.get("failed_hints") or []:
            if isinstance(failed, dict):
                failed_hints.append(failed)

    if lifecycle:
        mechanical["lemma_lifecycle"] = {
            "equation": lifecycle.get("equation"),
            "parsed": lifecycle.get("parsed"),
            "small_model_plausible": lifecycle.get("small_model_plausible"),
            "proved": lifecycle.get("proved"),
            "proof_source": lifecycle.get("proof_source"),
            "used_for_goal": lifecycle.get("used_for_goal"),
            "use_source": lifecycle.get("use_source"),
            "standard_kind": lifecycle.get("standard_kind"),
            "square_sandwich_kind": lifecycle.get("square_sandwich_kind"),
        }
        if lifecycle.get("proved"):
            proved_artifacts.append({
                "kind": "lemma",
                "equation": lifecycle.get("equation"),
                "source": lifecycle.get("proof_source"),
                "used_for_goal": lifecycle.get("used_for_goal"),
            })
        elif lifecycle.get("equation"):
            failed_hints.append({
                "kind": "lemma",
                "equation": lifecycle.get("equation"),
                "failure": attempt.get("error_code"),
            })

    if module_state:
        module_kind = module_state.get("kind")
        mechanical["module"] = {
            "kind": module_kind,
            "status": module_state.get("status"),
            "attempt_count": module_state.get("attempt_count"),
            "accepted_count": module_state.get("accepted_count"),
            "error_counts": module_state.get("error_counts"),
        }
        if module_kind == "false_model_search_state":
            trials = module_state.get("search_trials") or []
            need_hint = _as_dict(module_state.get("need_hint"))
            near_misses = []
            propagation_runs = []
            for trial in trials:
                if not isinstance(trial, dict):
                    continue
                diag = _as_dict(trial.get("diagnostics"))
                if diag.get("kind") == "propagation_model_finder_diagnostics":
                    best_partial = _as_dict(diag.get("best_partial"))
                    profile = _as_dict(best_partial.get("profile"))
                    eq2_partial = _as_dict(best_partial.get("eq2_partial"))
                    propagation_runs.append({
                        "route": trial.get("route"),
                        "status": trial.get("status"),
                        "size": diag.get("size"),
                        "nodes": diag.get("nodes"),
                        "node_cap": diag.get("node_cap"),
                        "forced_assignments": diag.get("forced_assignments"),
                        "conflicts": diag.get("conflicts"),
                        "forced_cells": diag.get("forced_cells"),
                        "blocked_cells": diag.get("blocked_cells"),
                        "branch_cells": diag.get("branch_cells"),
                        "best_partial_assigned_ratio": profile.get("assigned_ratio"),
                        "best_partial_unassigned_count": profile.get("unassigned_count"),
                        "best_partial_eq2_violations": eq2_partial.get("determined_violations"),
                        "best_partial_eq2_determined": eq2_partial.get("determined_assignments"),
                        "initial_constraints": diag.get("initial_constraints"),
                    })
                best = _as_dict(diag.get("best_near_miss"))
                candidates = [best] if best else []
                for alternate in diag.get("alternate_near_misses") or []:
                    if isinstance(alternate, dict):
                        candidates.append(alternate)
                for candidate in candidates:
                    if not candidate:
                        continue
                    near_misses.append({
                        "route": trial.get("route"),
                        "interpretation": diag.get("interpretation"),
                        "size": candidate.get("size"),
                        "h_violations": candidate.get("h_violations"),
                        "h_violation_ratio": candidate.get("h_violation_ratio"),
                        "g_failures": candidate.get("g_failures"),
                        "g_failure_ratio": candidate.get("g_failure_ratio"),
                        "h_hot_cells": candidate.get("h_hot_cells"),
                        "g_failure_hot_cells": candidate.get("g_failure_hot_cells"),
                    })
            mechanical["false_search"] = {
                "tried_routes": [
                    trial.get("route")
                    for trial in trials
                    if isinstance(trial, dict) and trial.get("route")
                ],
                "trial_statuses": [
                    {
                        "route": trial.get("route"),
                        "status": trial.get("status"),
                        "elapsed": trial.get("elapsed"),
                    }
                    for trial in trials
                    if isinstance(trial, dict)
                ],
                "untried_requested_routes": need_hint.get("untried_requested_routes"),
                "best_near_misses": near_misses[:4],
                "propagation_runs": propagation_runs[:4],
                "counterexample_size": module_state.get("counterexample_size"),
                "false_model_source": module_state.get("false_model_source"),
                "local_check": module_state.get("local_check"),
            }
            budgets["false_search_budget"] = module_state.get("budget_seconds")
            budgets["false_search_spent"] = module_state.get("search_budget_spent")
            budgets["false_search_remaining"] = module_state.get("budget_remaining")
        elif module_kind == "square_sandwich_chain":
            mechanical["lemma_chain"] = {
                "status": module_state.get("status"),
                "helper_lemmas": module_state.get("helper_lemmas"),
                "lhs_normal_form": module_state.get("lhs_normal_form"),
                "rhs_normal_form": module_state.get("rhs_normal_form"),
            }
            if module_state.get("helper_lemmas"):
                proved_artifacts.append({
                    "kind": "lemma_chain",
                    "helpers": module_state.get("helper_lemmas"),
                })
        elif module_kind == "forward_saturation_tool":
            mechanical["tool"] = {
                "tool": module_state.get("tool"),
                "status": module_state.get("status"),
                "target": module_state.get("target"),
                "seed_terms": module_state.get("seed_terms"),
                "invalid_seed_terms": module_state.get("invalid_seed_terms"),
                "attempt_count": module_state.get("attempt_count"),
                "generated_terms": module_state.get("generated_terms"),
                "generated_h_args": module_state.get("generated_h_args"),
                "trials": [
                    {
                        "config": trial.get("config"),
                        "status": trial.get("status"),
                        "error_code": trial.get("error_code"),
                        "consumer": trial.get("consumer"),
                        "graph_path_found": trial.get("graph_path_found"),
                        "fact_count": trial.get("fact_count"),
                        "pool_size": trial.get("pool_size"),
                    }
                    for trial in module_state.get("trials") or []
                    if isinstance(trial, dict)
                ][:4],
            }
            budgets["tool_budget"] = module_state.get("budget_seconds")
            budgets["tool_elapsed"] = module_state.get("elapsed")
        elif module_kind == "superposition_tool":
            mechanical["tool"] = {
                "tool": module_state.get("tool"),
                "status": module_state.get("status"),
                "target": module_state.get("target"),
                "attempt_count": module_state.get("attempt_count"),
                "accepted_count": module_state.get("accepted_count"),
                "error_counts": module_state.get("error_counts"),
                "verify_timeout_seconds": module_state.get("verify_timeout_seconds"),
                "include_aux": module_state.get("include_aux"),
                "include_goal": module_state.get("include_goal"),
                "implied_aux": module_state.get("implied_aux"),
                "attempts": [
                    {
                        "source": attempt.get("source"),
                        "status": attempt.get("status"),
                        "error_code": attempt.get("error_code"),
                        "body_excerpt": attempt.get("body_excerpt"),
                    }
                    for attempt in module_state.get("attempts") or []
                    if isinstance(attempt, dict)
                ][:3],
            }
            budgets["tool_budget"] = module_state.get("budget_seconds")
            budgets["tool_elapsed"] = module_state.get("elapsed")
        elif module_kind == "certificates_tool":
            mechanical["tool"] = {
                "tool": module_state.get("tool"),
                "status": module_state.get("status"),
                "target": module_state.get("target"),
                "attempt_count": module_state.get("attempt_count"),
                "accepted_count": module_state.get("accepted_count"),
                "error_counts": module_state.get("error_counts"),
                "verify_timeout_seconds": module_state.get("verify_timeout_seconds"),
                "attempts": [
                    {
                        "source": attempt.get("source"),
                        "status": attempt.get("status"),
                        "error_code": attempt.get("error_code"),
                        "body_excerpt": attempt.get("body_excerpt"),
                    }
                    for attempt in module_state.get("attempts") or []
                    if isinstance(attempt, dict)
                ][:3],
            }
            budgets["tool_budget"] = module_state.get("budget_seconds")
            budgets["tool_elapsed"] = module_state.get("elapsed")

    need_hint = _state_need_hint(module_state, result, search_state)
    state = {
        "kind": "collaboration_state",
        "round": attempt.get("round"),
        "status": attempt.get("status"),
        "error_code": attempt.get("error_code"),
        "hint": hint_summary,
        "mechanical": mechanical,
        "proved_artifacts": proved_artifacts[:8],
        "failed_hints": failed_hints[:8],
        "need_hint": need_hint,
        "budgets": {k: v for k, v in budgets.items() if v is not None},
    }
    return state


def _component_from_facts(seed: str, facts: list[dict[str, Any]]) -> set[str]:
    adjacency: dict[str, set[str]] = {}
    for fact in facts:
        adjacency.setdefault(fact["lhs"], set()).add(fact["rhs"])
        adjacency.setdefault(fact["rhs"], set()).add(fact["lhs"])
    seen = {seed}
    queue = [seed]
    while queue:
        current = queue.pop(0)
        for nxt in adjacency.get(current, set()):
            if nxt not in seen:
                seen.add(nxt)
                queue.append(nxt)
    return seen


def lemma_instance_diagnostics(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    limit: int,
    *,
    lemma: dict[str, Any],
    extra_args: list[tuple[str, ...]] | None = None,
    lemma_fact_limit: int = 96,
    congruence_depth: int = 0,
    max_congruence_facts: int = 240,
) -> dict[str, Any]:
    base_facts = _build_graph_facts(
        h_eq,
        g_eq,
        limit,
        extra_args=extra_args,
        congruence_depth=congruence_depth,
        max_congruence_facts=max_congruence_facts,
    )
    left = solver_core.term_to_str(g_eq["lhs"])
    right = solver_core.term_to_str(g_eq["rhs"])
    left_comp = _component_from_facts(left, base_facts)
    right_comp = _component_from_facts(right, base_facts)

    lemma_eq = lemma["eq"]
    rows = candidate_lemma_args(
        lemma_eq,
        g_eq,
        lemma_fact_limit,
        extra_args=lemma.get("extra_args") or [],
    )
    touching: list[dict[str, Any]] = []
    bridges: list[dict[str, Any]] = []
    for args in rows:
        lhs, rhs = render_lemma_type(lemma_eq, args)
        left_touch = lhs in left_comp or rhs in left_comp
        right_touch = lhs in right_comp or rhs in right_comp
        bridge = (
            (lhs in left_comp and rhs in right_comp)
            or (rhs in left_comp and lhs in right_comp)
        )
        item = {
            "args": list(args),
            "lhs": lhs,
            "rhs": rhs,
            "touches_left_component": left_touch,
            "touches_right_component": right_touch,
            "bridges_components": bridge,
        }
        if bridge:
            bridges.append(item)
        if left_touch or right_touch:
            touching.append(item)

    return {
        "kind": "lemma_instance_diagnostics",
        "lemma": lemma_eq["text"],
        "instances_tried": len(rows),
        "base_left_component_size": len(left_comp),
        "base_right_component_size": len(right_comp),
        "touching_instances": touching[:12],
        "bridge_instances": bridges[:6],
        "summary": (
            "at least one lemma instance bridges the graph components"
            if bridges
            else (
                "some lemma instances touch a component, but none bridge both"
                if touching
                else "no tried lemma instance touched either goal component"
            )
        ),
    }


def problem_context(problem: dict[str, Any], h_eq: dict[str, Any], g_eq: dict[str, Any]) -> str:
    try:
        analysis = solver_core._solver_analysis(h_eq, g_eq)
    except Exception as exc:  # noqa: BLE001
        analysis = f"(solver analysis failed: {type(exc).__name__}: {exc})"
    return (
        f"Problem {problem.get('id')}:\n"
        f"  h    : {solver_core.normalize(problem['equation1'])}\n"
        f"  goal : {solver_core.normalize(problem['equation2'])}\n\n"
        f"Hypothesis variables: {h_eq['variables']}\n"
        f"Goal variables, in exact intro order: {g_eq['variables']}\n\n"
        f"{hypothesis_schema(h_eq)}\n\n"
        "Mechanical analysis:\n"
        f"{analysis}\n"
    )


def false_problem_context(problem: dict[str, Any], h_eq: dict[str, Any], g_eq: dict[str, Any]) -> str:
    return (
        f"Problem {problem.get('id')}:\n"
        f"  H    : {solver_core.normalize(problem['equation1'])}\n"
        f"  G    : {solver_core.normalize(problem['equation2'])}\n\n"
        "False-side task: propose finite-model search hints for a magma where H "
        "holds for all assignments and G fails for at least one assignment. "
        "The mechanical side will perform the exhaustive table check and only "
        "accept a fully verified countermodel.\n\n"
        f"Hypothesis variables: {h_eq['variables']}\n"
        f"Goal variables: {g_eq['variables']}\n"
        "Known hard-false pattern: if small carriers are exhausted or time out, "
        "try a larger carrier with a noncommutative local-search template before "
        "asking for a full table.\n"
    )


STANDARD_HELPER_EQUATIONS = {
    "const": "a = b",
    "proj_l": "a ◇ b = a",
    "proj_r": "a ◇ b = b",
    "rowconst": "a ◇ b = a ◇ c",
}


def standard_helper_prompt_block(h_eq: dict[str, Any], mode: str) -> str:
    if mode not in ("lemma_hint", "lemma_chain"):
        return ""
    try:
        implied = solver_core.implied_aux_lemmas(h_eq) if h_eq.get("free") else []
    except Exception:  # noqa: BLE001
        implied = []
    if not implied:
        return (
            "Machine-readable standard helper advice:\n"
            "{\n"
            '  "include_standard_helpers": [],\n'
            '  "avoid_standard_helpers": ["a = b", "a ◇ b = a", "a ◇ b = b", "a ◇ b = a ◇ c"],\n'
            '  "reason": "small-model filter refutes the standard helpers for this H"\n'
            "}\n\n"
        )
    equations = [STANDARD_HELPER_EQUATIONS[k] for k in implied if k in STANDARD_HELPER_EQUATIONS]
    return (
        "Machine-readable standard helper advice:\n"
        + json.dumps({
            "include_standard_helpers": equations,
            "reason": "small-model filter did not refute these helpers; include them as candidates",
        }, ensure_ascii=False, indent=2)
        + "\n\n"
    )


FEWSHOT_DIRECT = """A valid proof body has this shape. Notice that `h` is a
universally quantified hypothesis, so `h A B C ...` instantiates the variables
of the hypothesis equation.

Toy example:
  h    : x ◇ y = y ◇ x
  goal : x ◇ (y ◇ z) = (y ◇ z) ◇ x

One accepted body:
```lean
intro x y z
have h1 := h x (y ◇ z)
simpa using h1
```

For the current problem, use the same style: instantiate `h` on concrete terms,
name the useful facts, then connect them with `calc`, `simpa using ...`, or
small explicit rewrites. Do not write comments or placeholders inside the proof
string.
"""

FEWSHOT_FALSE_HINT = """Useful false-model hints are search controls, not proofs.
The mechanical side will complete/check the table.

Example when small sizes were exhausted:
```json
{
  "kind": "false_model_hint",
  "template": "local_search",
  "sizes": [6, 7],
  "seeds": [0, 1, 2],
  "time_budget": 18,
  "constraints": ["noncommutative", "allow repeated rows"],
  "rationale": "n<=4 has no model; try a larger noncommutative repair search."
}
```

Example when a closed family looks plausible:
```json
{
  "kind": "false_model_hint",
  "template": "quadratic_mod_n",
  "carrier_size": 7,
  "rationale": "The terms repeat x and y in polynomial-looking positions."
}
```

Example after propagation reports branch/blocked cells:
```json
{
  "kind": "false_model_hint",
  "template": "propagation",
  "routes": ["find_model:n7"],
  "focus_cells": [[0, 1], [2, 3]],
  "time_budget": 6,
  "rationale": "Continue the bounded model finder at the size whose branch cells looked most constrained."
}
```

Example after `best_near_misses` reports H-hotspot cells:
```json
{
  "kind": "false_model_hint",
  "template": "focused_local_search",
  "routes": ["local_search:n=6:seed=2"],
  "focus_cells": [[1, 2], [1, 3], [2, 1]],
  "constraints": ["repair H-hotspot cells while preserving G failure"],
  "time_budget": 6,
  "rationale": "G already failed in a near-model; focus repair on the H-hotspot cells."
}
```
"""


FEWSHOT_TOOL_CALL = """Tool calls are requests to run one trusted mechanical module.
The module may return an accepted Lean proof, or a structured stuck state for the
next round.

Example:
```json
{
  "kind": "tool_call",
  "tool": "forward_saturation",
  "target": "goal",
  "seed_terms": ["x ◇ y", "y ◇ y", "(x ◇ y) ◇ x"],
  "budget": 3,
  "why": "Try generated h-instances around the repeated y-square terms."
}
```

Example old proof-battery call:
```json
{
  "kind": "tool_call",
  "tool": "proof_battery",
  "target": "goal",
  "budget": 18,
  "max_candidates": 5,
  "why": "Try the old deterministic HAVE+GRIND battery before heavier proof search."
}
```

Example when the mechanical modules ask for a bridge lemma:
```json
{
  "kind": "tool_call",
  "tool": "lemma_hint",
  "target": "goal",
  "lemmas": ["a ◇ b = a ◇ c", "x ◇ y = x"],
  "why": "Ask the trusted lemma consumer to prove/use a small bridge equation."
}
```

Accepted seed-argument pattern. In this toy, `h` has four arguments, so every
`seed_h_args` row has exactly four entries. The equation is not trusted; these
rows just tell the mechanical side which `h` instances to try while proving the
lemma:
```json
{
  "kind": "tool_call",
  "tool": "lemma_hint",
  "target": "goal",
  "lemmas": [
    {
      "equation": "x ◇ (x ◇ y) = z ◇ (y ◇ y)",
      "seed_h_args": [
        ["x", "(x ◇ y)", "y", "y"],
        ["(x ◇ y)", "((y ◇ y) ◇ y)", "y", "y"],
        ["z", "(y ◇ y)", "y", "y"],
        ["(y ◇ y)", "((y ◇ y) ◇ y)", "y", "y"]
      ],
      "use_args": [["x", "y", "z"]]
    }
  ],
  "why": "The lemma touches both goal frontiers and the h-rows create the proof path."
}
```

Repair pattern after feedback says a lemma was proved but unused: do not repeat
another left-only fact. Propose a bridge touching the missing `left_term` and
`right_term`, and give concrete `seed_h_args` rows. Use the exact field
`seed_h_args`; if you accidentally return rows in `seed_h_args_template`, the
sidecar will treat them as `seed_h_args`.

Concrete hard-bridge repair shape:
```json
{
  "kind": "tool_call",
  "tool": "lemma_hint",
  "target": "goal",
  "lemmas": [
    {
      "equation": "((x ◇ (x ◇ x)) ◇ (x ◇ x)) = x ◇ ((y ◇ (x ◇ y)) ◇ x)",
      "seed_h_args": [
        ["x", "x", "x"],
        ["((y ◇ (x ◇ y)) ◇ x)", "x", "x"],
        ["(y ◇ (x ◇ y))", "x", "x"],
        ["(x ◇ y)", "x", "x"]
      ]
    }
  ],
  "why": "A previous lemma proved only the left side and was unused; this tries the missing bridge with concrete h rows."
}
```

Example when feedback says the hypothesis has a square-witness helper shape:
```json
{
  "kind": "tool_call",
  "tool": "lemma_chain",
  "target": "goal",
  "lemmas": [
    {"name": "square_const", "equation": "u ◇ u = v ◇ v"},
    {"name": "right_id_square", "equation": "u ◇ (v ◇ v) = u"},
    {"name": "sandwich", "equation": "(v ◇ u) ◇ v = u"},
    {"name": "left_sandwich", "equation": "v ◇ (u ◇ v) = u"}
  ],
  "why": "Ask the trusted chain consumer to prove and use the square-witness helpers."
}
```

Example when feedback says the hypothesis has a right-square absorption shape:
```json
{
  "kind": "tool_call",
  "tool": "right_square_chain",
  "target": "goal",
  "budget": 15,
  "why": "Use the trusted renderer that proves u ◇ (v ◇ v) = v and u ◇ v = v ◇ v, then stitches the goal explicitly."
}
```

The same right-square proof can also be expressed through the generic
multi-lemma chain consumer:
```json
{
  "kind": "tool_call",
  "tool": "lemma_chain",
  "target": "goal",
  "lemmas": [
    {"name": "square_absorb", "equation": "u ◇ (v ◇ v) = v"},
    {"name": "right_square", "equation": "u ◇ v = v ◇ v"}
  ],
  "why": "Ask the generic chain consumer to prove the right-square helpers and use them together."
}
```

Example false-side tool call:
```json
{
  "kind": "tool_call",
  "tool": "false_model_search",
  "target": "goal",
  "template": "local_search",
  "sizes": [5, 6],
  "seeds": [0, 1, 2],
  "budget": 8,
  "why": "Search for a finite countermodel with a fixed small budget."
}
```
"""


TOOL_REGISTRY: dict[str, dict[str, Any]] = {
    "forward_saturation": {
        "domain": "true",
        "aliases": ["saturation"],
        "description": "Generate h-instantiations from goal/seed terms and try graph/grind consumers.",
    },
    "proof_battery": {
        "domain": "true",
        "aliases": ["battery", "have_grind_battery", "old_battery", "deterministic_battery"],
        "description": "Run the old deterministic HAVE+GRIND proof battery, including optional implied auxiliary lemmas.",
    },
    "goal_superposition": {
        "domain": "true",
        "aliases": ["superposition"],
        "description": "Run proof-carrying whole-goal superposition.",
    },
    "square_sandwich_chain": {
        "domain": "true",
        "aliases": ["square_chain", "sandwich_chain", "square_witness_chain"],
        "description": "Try square-constant/right-identity/sandwich helper-chain renderers.",
    },
    "right_square_chain": {
        "domain": "true",
        "aliases": ["right_square_absorb", "square_absorb_chain", "right_square_absorption"],
        "description": "Try the right-square/square-absorption helper-chain renderer.",
    },
    "certificates": {
        "domain": "true",
        "aliases": ["cert", "certificate", "standard_certificates", "cert_candidates"],
        "description": "Run a bounded slice of old proof-certificate renderers.",
    },
    "rowconst_certificates": {
        "domain": "true",
        "aliases": ["rowconst_certificate", "square_rowconst_certificate", "explicit_rowconst", "explicit_square_rowconst"],
        "description": "Run focused old row-constant and square-rowconstant certificate renderers.",
    },
    "grounding_derived": {
        "domain": "true",
        "aliases": ["grounding_certificates", "derived_grounding", "cert_ground_derived", "grounding_derived_cert"],
        "description": "Run the old grounding-derived certificate renderer for non-orientable helper lemmas.",
    },
    "lemma_hint": {
        "domain": "true",
        "aliases": ["lemma", "lemma_tool", "midpoint", "midpoint_hint", "bridge_lemma"],
        "description": "Prove and consume one or more untrusted bridge equations.",
    },
    "lemma_chain": {
        "domain": "true",
        "aliases": ["chain", "helper_chain", "lemma_sequence"],
        "description": "Prove and consume a sequence of helper equations.",
    },
    "false_model_search": {
        "domain": "false",
        "aliases": [
            "countermodel_search",
            "finite_model_search",
            "false_model_hint",
            "model_finder",
            "local_search",
            "focused_local_search",
            "propagation",
        ],
        "description": "Search for or verify finite countermodels using the false-model machinery.",
    },
}


TOOL_ALIASES: dict[str, str] = {
    alias: name
    for name, spec in TOOL_REGISTRY.items()
    for alias in [name, *spec.get("aliases", [])]
}


def normalize_tool_name(tool: str) -> str:
    key = str(tool or "").strip().lower()
    return TOOL_ALIASES.get(key, key)


def tool_registry_prompt_specs() -> list[dict[str, Any]]:
    return [
        {
            "tool": name,
            "domain": spec.get("domain"),
            "aliases": spec.get("aliases", [])[:5],
            "description": spec.get("description"),
        }
        for name, spec in TOOL_REGISTRY.items()
    ]


def _attempt_tool_name(attempt: dict[str, Any]) -> str | None:
    tool_call = _as_dict(attempt.get("tool_call"))
    module_state = _as_dict(attempt.get("module_state"))
    tool = tool_call.get("tool") or module_state.get("tool")
    return normalize_tool_name(str(tool)) if tool else None


def _module_need_hint(attempt: dict[str, Any]) -> dict[str, Any]:
    module_state = _as_dict(attempt.get("module_state"))
    return _as_dict(module_state.get("need_hint"))


def _normal_tool_call(raw_call: dict[str, Any]) -> dict[str, Any]:
    seed_terms = raw_call.get("seed_terms") or raw_call.get("terms") or raw_call.get("seeds") or []
    if isinstance(seed_terms, str):
        seed_terms = [seed_terms]
    if not isinstance(seed_terms, list):
        seed_terms = []
    call = {
        "kind": "tool_call",
        "tool": normalize_tool_name(str(raw_call.get("tool") or "forward_saturation")),
        "target": str(raw_call.get("target") or "goal"),
        "budget": float(raw_call.get("budget") or raw_call.get("time_budget") or 3.0),
        "why": str(raw_call.get("why") or raw_call.get("rationale") or "")[:500],
    }
    if seed_terms:
        call["seed_terms"] = [str(term) for term in seed_terms if str(term).strip()]
    for key in ("max_candidates", "include_aux", "include_goal", "max_bodies"):
        if key in raw_call:
            call[key] = raw_call[key]
    return call


def _call_signature(call: dict[str, Any]) -> str:
    return json.dumps(_normal_tool_call(call), ensure_ascii=False, sort_keys=True)


def _recent_tool_failures(previous: list[dict[str, Any]]) -> dict[str, int]:
    failures: dict[str, int] = {}
    for attempt in previous:
        if attempt.get("status") == "accepted":
            continue
        tool = _attempt_tool_name(attempt)
        if tool:
            failures[tool] = failures.get(tool, 0) + 1
    return failures


def _last_failed_tool(previous: list[dict[str, Any]]) -> str | None:
    for attempt in reversed(previous):
        if attempt.get("status") == "accepted":
            continue
        tool = _attempt_tool_name(attempt)
        if tool:
            return tool
    return None


def _shape_tool_suggestions(previous: list[dict[str, Any]]) -> list[dict[str, Any]]:
    suggestions: list[dict[str, Any]] = []
    for attempt in previous[-3:]:
        need_hint = _module_need_hint(attempt)
        shape = need_hint.get("next_tool_call_shape")
        if isinstance(shape, dict):
            suggestions.append(_normal_tool_call(shape))
        shapes = need_hint.get("next_tool_call_shapes")
        if isinstance(shapes, list):
            for item in shapes:
                if isinstance(item, dict):
                    suggestions.append(_normal_tool_call(item))
    return suggestions


def _llm_tool_templates(previous: list[dict[str, Any]]) -> list[dict[str, Any]]:
    templates: list[dict[str, Any]] = []
    for attempt in previous[-3:]:
        need_hint = _module_need_hint(attempt)
        raw_templates = need_hint.get("llm_tool_call_templates")
        if isinstance(raw_templates, list):
            for item in raw_templates:
                if isinstance(item, dict):
                    templates.append(item)
    return templates


def tool_recommendations(
    *,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    previous: list[dict[str, Any]],
    max_items: int = 4,
) -> dict[str, Any]:
    """Cheap, non-verifying router advice for tool_call mode."""
    goal_terms = solver_core.goal_term_pool(g_eq, max_terms=6)
    failures = _recent_tool_failures(previous)
    last_failed_tool = _last_failed_tool(previous)
    already_tried = {
        _call_signature(_as_dict(attempt.get("tool_call")))
        for attempt in previous
        if attempt.get("tool_call")
    }
    by_tool: dict[str, dict[str, Any]] = {}

    def add(
        *,
        tool: str,
        score: float,
        why: list[str],
        call: dict[str, Any] | None = None,
        cautions: list[str] | None = None,
    ) -> None:
        base_call = _normal_tool_call(call or {
            "kind": "tool_call",
            "tool": tool,
            "target": "goal",
            "budget": 3.0,
            "why": why[0] if why else "",
        })
        base_call["tool"] = tool
        if not base_call.get("why") and why:
            base_call["why"] = why[0]
        penalty = 0.0
        if failures.get(tool):
            penalty += min(30.0, 12.0 * failures[tool])
        if tool == last_failed_tool and failures.get(tool, 0) >= 2:
            penalty += 35.0
        if _call_signature(base_call) in already_tried:
            penalty += 25.0
        diversity_bonus = 18.0 if previous and not failures.get(tool) else 0.0
        adjusted = max(0.0, score + diversity_bonus - penalty)
        item_why = list(why)
        if diversity_bonus:
            item_why.append("this tool has not yet been tried in the current run")
        item = by_tool.get(tool)
        if item is None or adjusted > item["score"]:
            by_tool[tool] = {
                "tool": tool,
                "score": round(adjusted, 1),
                "why": _unique(item_why),
                "call": base_call,
                "cautions": _unique(cautions or []),
            }

    rowconst_body = special_rowconst_body(h_eq, g_eq)
    square_rowconst_body = special_square_rowconst_body(h_eq, g_eq)
    if rowconst_body is not None or square_rowconst_body is not None:
        add(
            tool="rowconst_certificates",
            score=99,
            why=[
                "a focused row-constant certificate renderer appears applicable to this exact H/G shape",
                "this should be tried before broader search because it returns a kernel-checked proof body",
            ],
            call={
                "kind": "tool_call",
                "tool": "rowconst_certificates",
                "target": "goal",
                "budget": 15,
                "max_candidates": 3,
                "why": "Run the focused row-constant certificate consumer for the detected shape.",
            },
        )
    elif _special_square_rowconst_h_vars(h_eq) is not None or _special_rowconst_h_vars(h_eq) is not None:
        add(
            tool="rowconst_certificates",
            score=82,
            why=[
                "H matches a row-constant family handled by the certificate module",
                "goal shape was not an exact explicit hit, so keep this below direct shape hits",
            ],
            call={
                "kind": "tool_call",
                "tool": "rowconst_certificates",
                "target": "goal",
                "budget": 12,
                "max_candidates": 5,
                "why": "Try focused row-constant certificate candidates for the detected family.",
            },
        )

    square_chain_body, square_chain_state = special_square_sandwich_chain_body(h_eq, g_eq)
    if square_chain_body is not None:
        add(
            tool="square_sandwich_chain",
            score=98,
            why=[
                "H has square-sandwich shape and the helper-chain normalizer closes the goal shape",
                "this tool emits the full square-constant/right-identity/sandwich chain",
            ],
            call={
                "kind": "tool_call",
                "tool": "square_sandwich_chain",
                "target": "goal",
                "budget": 15,
                "why": "Run the square-witness helper-chain renderer; the shape analysis says it should close.",
            },
        )
    elif _special_square_sandwich_h_vars(h_eq) is not None:
        add(
            tool="square_sandwich_chain",
            score=76,
            why=[
                "H has square-sandwich shape",
                f"the reducer currently reports {square_chain_state.get('status')}",
            ],
            call={
                "kind": "tool_call",
                "tool": "square_sandwich_chain",
                "target": "goal",
                "budget": 10,
                "why": "Probe the square-witness chain and return the normal-form gap if it does not close.",
            },
            cautions=["may only produce a useful stuck state if the current helper simplifier is too weak"],
        )

    right_square_body = special_right_square_absorb_body(h_eq, g_eq)
    if right_square_body is not None:
        add(
            tool="right_square_chain",
            score=98,
            why=[
                "H matches the right-square absorption family and the explicit helper-chain renderer closes the goal",
                "this tool proves square_absorb/right_square helpers and stitches the final goal without relying on grind",
            ],
            call={
                "kind": "tool_call",
                "tool": "right_square_chain",
                "target": "goal",
                "budget": 15,
                "why": "Run the right-square/square-absorption helper-chain renderer for the detected shape.",
            },
        )
    elif _special_right_square_absorb_h_vars(h_eq) is not None:
        add(
            tool="right_square_chain",
            score=74,
            why=[
                "H matches the right-square absorption family",
                "the current goal is not the exact supported absorption shape, so this may only return structured feedback",
            ],
            call={
                "kind": "tool_call",
                "tool": "right_square_chain",
                "target": "goal",
                "budget": 10,
                "why": "Probe the right-square/square-absorption renderer and report the shape gap.",
            },
            cautions=["currently focused on goals of the form a = a ◇ ((b ◇ (a ◇ b)) ◇ a)"],
        )

    add(
        tool="proof_battery",
        score=44 if not by_tool else 38,
        why=[
            "cheap old HAVE+GRIND proof battery with verifier-checked bodies",
            "currently kept low priority because early flywheel checks show mostly structured feedback, not accepted proofs",
        ],
        call={
            "kind": "tool_call",
            "tool": "proof_battery",
            "target": "goal",
            "budget": 8,
            "max_candidates": 1,
            "include_aux": True,
            "why": "Run the old deterministic HAVE+GRIND proof battery.",
        },
    )
    add(
        tool="forward_saturation",
        score=70,
        why=[
            "general cheap bridge search over h-instantiations",
            "goal frontier terms provide concrete seed_terms for the mechanical side",
        ],
        call={
            "kind": "tool_call",
            "tool": "forward_saturation",
            "target": "goal",
            "seed_terms": goal_terms,
            "budget": 5,
            "why": "Use goal-frontier seed terms to generate h-instantiations and try the h-fact graph.",
        },
    )
    add(
        tool="goal_superposition",
        score=48 if by_tool else 60,
        why=[
            "broad proof-carrying search over the whole goal",
            "useful fallback when no specialized H-shape has been detected",
        ],
        call={
            "kind": "tool_call",
            "tool": "goal_superposition",
            "target": "goal",
            "budget": 8,
            "max_candidates": 3,
            "include_aux": False,
            "why": "Try whole-goal proof-carrying superposition as a broad fallback.",
        },
    )

    for suggested in _shape_tool_suggestions(previous):
        tool = suggested.get("tool")
        if tool not in {
            "proof_battery",
            "forward_saturation",
            "goal_superposition",
            "square_sandwich_chain",
            "right_square_chain",
            "certificates",
            "rowconst_certificates",
            "grounding_derived",
        }:
            continue
        if failures.get(tool, 0) >= 2:
            continue
        add(
            tool=tool,
            score=86,
            why=["a previous mechanical module explicitly requested this next tool-call shape"],
            call=suggested,
        )

    ranked = sorted(by_tool.values(), key=lambda item: (-item["score"], item["tool"]))[:max_items]
    for idx, item in enumerate(ranked, start=1):
        item["rank"] = idx
    llm_only_actions = _llm_tool_templates(previous)
    if failures.get("forward_saturation") and failures.get("goal_superposition") and not llm_only_actions:
        llm_only_actions.append({
            "kind": "tool_call",
            "tool": "lemma_hint",
            "target": "goal",
            "lemmas": [
                "<small bridge equation involving the goal frontier>",
                "<local simplification equation that the mechanical side can prove from h>",
            ],
            "why": (
                "forward_saturation and goal_superposition both got stuck; "
                "provide untrusted bridge lemmas for the mechanical lemma consumer"
            ),
            "requires_llm_content": True,
        })
    recommended_next_action: dict[str, Any] | None = None
    recommendation_note = ""
    if llm_only_actions and (
        failures.get("forward_saturation", 0) >= 2
        or failures.get("goal_superposition")
        or failures.get("lemma_hint")
        or failures.get("lemma_chain")
    ):
        recommended_next_action = llm_only_actions[-1]
        recommendation_note = (
            "Mechanical calls have already stalled. Fill this LLM-only template "
            "with concrete equations instead of repeating a ranked mechanical call."
        )
    elif ranked:
        recommended_next_action = ranked[0]["call"]
        recommendation_note = "Use the highest-ranked executable mechanical call."
    return {
        "kind": "tool_recommendations",
        "problem_id": problem.get("id"),
        "recommended_next_action": recommended_next_action,
        "recommendation_note": recommendation_note,
        "ranked": ranked,
        "llm_only_actions": llm_only_actions,
        "already_failed_tools": failures,
        "selection_policy": (
            "Prefer the highest-ranked call. If it fails, use the returned module_state.need_hint "
            "to choose a different ranked tool or the requested next_tool_call_shape. "
            "If all ranked mechanical tools have already failed, prefer an llm_only_action "
            "such as lemma_hint and fill in concrete equations."
        ),
    }


def tool_recommendation_block(
    *,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    previous: list[dict[str, Any]],
    mode: str,
) -> str:
    if mode != "tool_call":
        return ""
    advice = tool_recommendations(problem=problem, h_eq=h_eq, g_eq=g_eq, previous=previous)
    urgent = ""
    if advice.get("llm_only_actions") and advice.get("recommended_next_action"):
        urgent = (
            "IMPORTANT: the recommended_next_action is an LLM-filled template. "
            "Return that kind of tool call with concrete equations; do not copy "
            "placeholder text and do not repeat a failed mechanical call unless "
            "you have genuinely new parameters.\n"
        )
    return (
        "Machine-readable mechanical tool-selection advice:\n"
        f"{urgent}"
        f"```json\n{search_state_text(advice, max_chars=5000)}\n```\n\n"
    )


def auto_tool_router_response(
    *,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    previous: list[dict[str, Any]],
) -> dict[str, Any]:
    advice = tool_recommendations(problem=problem, h_eq=h_eq, g_eq=g_eq, previous=previous)
    ranked = advice.get("ranked") or []
    if not ranked:
        call = {
            "kind": "tool_call",
            "tool": "forward_saturation",
            "target": "goal",
            "seed_terms": solver_core.goal_term_pool(g_eq, max_terms=6),
            "budget": 5,
            "why": "Default router fallback.",
        }
    else:
        call = dict(ranked[0]["call"])
    return {
        "response": json.dumps(call, ensure_ascii=False),
        "source": "auto_tool_router",
        "tool_recommendations": advice,
    }


def build_prompt(
    *,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    mode: str,
    previous: list[dict[str, Any]],
    include_fewshot: bool,
    max_h_facts: int,
) -> str:
    context = (
        false_problem_context(problem, h_eq, g_eq)
        if mode == "false_model_hint"
        else problem_context(problem, h_eq, g_eq)
    )
    fact_lines = candidate_h_facts(h_eq, g_eq, max_h_facts)
    if mode == "false_model_hint":
        fact_lines = []
    standard_helper_block = standard_helper_prompt_block(h_eq, mode)
    square_chain_block = _square_sandwich_chain_advice(h_eq, mode)
    tool_advice_block = tool_recommendation_block(
        problem=problem,
        h_eq=h_eq,
        g_eq=g_eq,
        previous=previous,
        mode=mode,
    )
    tool_registry_block = ""
    if mode == "tool_call":
        tool_registry_block = (
            "Machine-readable tool registry:\n"
            "```json\n"
            + search_state_text(tool_registry_prompt_specs(), max_chars=2500)
            + "\n```\n\n"
        )
    fewshot_block = (
        FEWSHOT_DIRECT
        if include_fewshot and mode in ("direct", "lemma")
        else (
            FEWSHOT_FALSE_HINT
            if include_fewshot and mode == "false_model_hint"
            else (FEWSHOT_TOOL_CALL if include_fewshot and mode == "tool_call" else "")
        )
    )
    fact_menu = ""
    if fact_lines:
        fact_intro = (
            "Mechanically generated exact h-instantiations already in the graph. "
            "Your hints should add new rows that are not just duplicates.\n"
            if mode == "hargs"
            else (
                "Mechanically generated exact h-instantiations available to prove "
                "or use an intermediate lemma or lemma chain.\n"
                if mode in ("lemma_hint", "lemma_chain")
                else (
                    "Mechanically generated exact h-instantiations you may use. "
                    "If a line is useful, copy its `have` line into your proof; the "
                    "displayed type is exactly what Lean will know.\n"
                )
            )
        )
        fact_menu = (
            fact_intro
            + "\n".join(fact_lines)
            + "\n\n"
        )
    wrapper = "" if mode in ("false_model_hint", "tool_call") else (
        "The verifier wraps your proof body like this:\n\n"
        "```lean\n"
        "import JudgeProblem\n\n"
        "set_option maxHeartbeats 12800000 in\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        "  <YOUR BODY HERE>\n"
        "```\n"
    )
    mode_instruction = {
        "direct": (
            "Try to prove the goal directly. Your body should usually start with "
            f"`intro {' '.join(g_eq['variables'])}` and then use `have ... := h ...` "
            "facts, `calc`, `rw`, `.trans`, `.symm`, and `simpa using named_fact`. "
            "Avoid `grind` in LLM-written proofs unless the feedback specifically asks for it."
        ),
        "lemma": (
            "Prefer a small explicit lemma first, then use it to close the goal. "
            "For example, emit a body containing `have mid : ∀ ... := by ...`, "
            f"then `intro {' '.join(g_eq['variables'])}` and finish the goal. "
            "The lemma must be proved from `h`; it is not trusted."
        ),
        "lemma_hint": (
            "Do not write a Lean proof. Propose one equational intermediate lemma, "
            "or a ranked short list of 3-8 candidate lemmas, as equation strings. "
            "Each candidate may include optional `seed_h_args` for proving that "
            "lemma from `h`, and optional `use_args` for using the lemma on the "
            "current goal. The sidecar will rank and prove candidates mechanically, "
            "then use accepted lemmas as named rewrite facts. Standard universal "
            "lemmas such as `a ◇ b = a ◇ c`, `a ◇ b = a`, `a ◇ b = b`, or `a = b` "
            "are especially useful when the mechanical analysis says they are "
            "implied; include any such implied standard helper as one candidate "
            "because it can activate specialized verified consumers. Prefer a "
            "smaller local rewrite or bridge lemma, not the exact current goal restated."
        ),
        "lemma_chain": (
            "Do not write a Lean proof. Propose a short named chain of universal "
            "equational helper lemmas that would simplify the goal. The sidecar "
            "will prove the whole chain mechanically and then render the final "
            "goal proof. For witness-square problems, the useful chain is often "
            "`u ◇ u = v ◇ v`, then `u ◇ (v ◇ v) = u`, then `(v ◇ u) ◇ v = u`, "
            "and sometimes the derived dual `v ◇ (u ◇ v) = u`."
        ),
        "hargs": (
            "Do not write a Lean proof. Instead propose additional instantiations "
            f"of `h`, which has {len(h_eq['variables'])} arguments in this order: "
            f"{h_eq['variables']}. The mechanical graph prover will add your "
            "facts to its generated facts and look for an equality path from the "
            "goal's left side to its right side. Good hints usually introduce "
            "compound terms that could be common reducts or bridges."
        ),
        "false_model_hint": (
            "Do not write Lean and do not claim a verdict. Propose finite-model "
            "search structure for refuting H => G. The sidecar will search and "
            "then exhaustively check any candidate countermodel. Good hints pick "
            "a carrier size, a template such as `local_search`, `focused_local_search`, "
            "`model_finder`, `affine_mod_n`, `quadratic_mod_n`, or `existing_families`, and a "
            "few seeds/constraints. If you know a full table, return it as "
            "`counterexample_table`, but prefer compact search hints."
        ),
        "tool_call": (
            "Do not write Lean and do not claim a verdict. Choose one trusted "
            "mechanical tool to run next. Available tools: `proof_battery`, "
            "`forward_saturation`, `goal_superposition`, `square_sandwich_chain`, "
            "`rowconst_certificates`, `certificates`, `grounding_derived`, "
            "`lemma_hint`, `lemma_chain`, and false-side `false_model_search`. "
            "If the module feedback asks for a bridge lemma or midpoint, you may "
            "also call `lemma_hint` with a `lemmas` list, or `lemma_chain` with a "
            "short chain of helper equations. `proof_battery` runs the old "
            "deterministic HAVE+GRIND battery and reports per-body verifier "
            "feedback. "
            "`forward_saturation` generates "
            "h-instantiations from goal and seed terms, tries the h-fact "
            "graph/calc renderer first, and verifies the resulting Lean proof. "
            "`goal_superposition` runs the proof-carrying superposition module "
            "on the whole goal. `square_sandwich_chain` tries the square-constant "
            "and sandwich-helper renderer for hypotheses like "
            "`x = ((y ◇ x) ◇ y) ◇ (z ◇ z)`. `rowconst_certificates` runs focused "
            "row-constant/square-rowconstant certificate renderers. `certificates` runs a small slice "
            "of the old proof-certificate renderers. `grounding_derived` runs "
            "the old grounding-derived certificate renderer directly. `lemma_hint` and "
            "`lemma_chain` do not trust the equations; they mechanically prove "
            "and use them before accepting. `false_model_search` delegates to "
            "the bounded finite-countermodel machinery and verifies any table "
            "it finds before accepting. Return seed terms only for "
            "`forward_saturation`; return equations only for `lemma_hint` or "
            "`lemma_chain`; return finite-search controls only for "
            "`false_model_search`. All equation terms must use current goal "
            "variables and `◇`."
        ),
    }[mode]

    attempts = ""
    if previous:
        parts = ["Previous attempts and Lean feedback:"]
        for item in previous[-3:]:
            collab_state = collaboration_state_from_attempt(item)
            parts.append(
                f"\nAttempt {item['round']} normalized CollaborationState:\n"
                f"```json\n{search_state_text(collab_state, max_chars=2500)}\n```\n"
            )
            shown_body = item.get("cleaned_body") or item.get("raw_body", "")
            if len(shown_body) > 2500:
                shown_body = shown_body[:2500] + "\n... (truncated)"
            parts.append(
                f"\nAttempt {item['round']} submitted artifact:\n"
                f"```lean\n{shown_body}\n```\n"
                f"Lean result: {item['status']} / {item.get('error_code')}\n"
                f"Lean feedback:\n{item['feedback']}\n"
            )
            if item.get("search_state"):
                parts.append(
                    "Mechanical SearchState after this attempt:\n"
                    f"```json\n{search_state_text(item['search_state'], max_chars=3500)}\n```\n"
                )
                need_hint = item["search_state"].get("need_hint")
                if need_hint:
                    parts.append(
                        "Most useful next hint requested by the mechanical side:\n"
                        f"```json\n{search_state_text(need_hint, max_chars=1000)}\n```\n"
                    )
            if item.get("lemma_lifecycle"):
                parts.append(
                    "Lemma lifecycle for this attempt:\n"
                    f"```json\n{search_state_text(item['lemma_lifecycle'], max_chars=1500)}\n```\n"
                )
            if item.get("module_state"):
                parts.append(
                    "Mechanical module state after this attempt:\n"
                    f"```json\n{search_state_text(item['module_state'], max_chars=3000)}\n```\n"
                )
                module_need_hint = item["module_state"].get("need_hint")
                if module_need_hint:
                    parts.append(
                        "Most useful next module-level hint requested by the mechanical side:\n"
                        f"```json\n{search_state_text(module_need_hint, max_chars=1500)}\n```\n"
                    )
        attempts = "\n".join(parts)
    else:
        attempts = "No previous attempts in this sidecar run."

    example_args = [g_eq["variables"][0] if g_eq["variables"] else "x"] * len(h_eq["variables"])
    if mode == "hargs":
        schema = json.dumps({"kind": "h_arg_hints", "h_args": [example_args]})
    elif mode == "false_model_hint":
        schema = json.dumps({
            "kind": "false_model_hint",
            "template": "local_search",
            "sizes": [5, 6, 7],
            "seeds": [0, 1, 2],
            "time_budget": 18,
            "constraints": ["noncommutative", "allow repeated rows"],
            "rationale": "n<=4 often has no model for hard false cases; try larger local repair.",
        })
    elif mode == "tool_call":
        schema = json.dumps({
            "kind": "tool_call",
            "tool": "forward_saturation",
            "target": "goal",
            "seed_terms": [
                g_eq["variables"][0] if g_eq["variables"] else "x",
            ],
            "budget": 3,
            "why": "Run forward saturation with a small term seed set.",
        })
    elif mode == "lemma_chain":
        schema = json.dumps({
            "kind": "lemma_chain",
            "lemmas": [
                {"name": "square_const", "equation": "u ◇ u = v ◇ v"},
                {"name": "right_id_square", "equation": "u ◇ (v ◇ v) = u"},
                {"name": "sandwich", "equation": "(v ◇ u) ◇ v = u"},
                {"name": "left_sandwich", "equation": "v ◇ (u ◇ v) = u"},
            ],
            "witness_term": f"{g_eq['variables'][0]} ◇ {g_eq['variables'][0]}" if g_eq["variables"] else "",
        })
    elif mode == "lemma_hint":
        schema = json.dumps({
            "kind": "lemma_hint",
            "lemmas": ["a ◇ b = a ◇ c", "x ◇ y = x ◇ z"],
            "seed_h_args": [example_args],
            "use_args": [["x", "y", "z"]],
        })
    else:
        schema = "{\"kind\":\"goal_proof\",\"proof\":\"<Lean tactic body after intro G _ h>\"}"
    extra_constraints = (
        "- In hargs mode, every `h_args` row must have exactly "
        f"{len(h_eq['variables'])} strings, one per h argument. Return 8-30 rows. "
        "Use only Lean terms built from current goal variables and `◇`.\n"
        if mode == "hargs"
        else ""
    )
    if mode == "lemma_hint":
        extra_constraints += (
            "- In lemma_hint mode, each equation must look like "
            "`x ◇ y = x ◇ z`; do not include `∀`, `by`, a lemma name, or proof text. "
            "You may return either one `equation` or a `lemmas`/`lemma_hints` list. "
            "Prefer a `lemmas` list with 3-8 candidates. If the mechanical analysis "
            "says a standard helper lemma is implied, include that helper exactly "
            "as one candidate, for example `a ◇ b = a ◇ c`. "
            "Do not use the exact goal equation as a lemma unless no smaller "
            "bridge is plausible. `seed_h_args` rows must have exactly "
            f"{len(h_eq['variables'])} strings. `use_args` rows must match the "
            "number of variables in your lemma equation.\n"
        )
    if mode == "lemma_chain":
        extra_constraints += (
            "- In lemma_chain mode, every lemma entry must be only an equation "
            "string or an object with `name` and `equation`; do not include "
            "`∀`, `by`, proof text, or Lean declarations. Prefer 2-5 lemmas. "
            "For square-witness chains, include all three required equations: "
            "`u ◇ u = v ◇ v`, `u ◇ (v ◇ v) = u`, and `(v ◇ u) ◇ v = u`; "
            "include `v ◇ (u ◇ v) = u` too when the stuck term has the shape "
            "`v ◇ (u ◇ v)`.\n"
        )
    if mode == "false_model_hint":
        extra_constraints += (
            "- In false_model_hint mode, return only model-search instructions. "
            "Allowed templates include `local_search`, `model_finder`, "
            "`focused_local_search`, `existing_families`, `affine_mod_n`, and `quadratic_mod_n`. "
            "Use `sizes` or `carrier_size` for carrier sizes. Use `seeds` for "
            "local_search. Only after a previous attempt shows "
            "`untried_requested_routes`, you may copy exact strings from that "
            "list into `routes` to prioritize those searches. A full "
            "`counterexample_table` is allowed only if you "
            "are intentionally proposing a complete finite magma table. If a "
            "previous false_model_search_state is shown, do not repeat an "
            "already tried route exactly; use the remaining budget to change "
            "the size, seed set, or search template. If `best_near_misses` says "
            "H is satisfied but G still holds, prefer a G-breaking size/template; "
            "if it says G already fails but H has hotspot cells, prefer a narrower "
            "`focused_local_search` route with `focus_cells` aimed at those H hotspots.\n"
            "If `propagation_runs` reports branch_cells or blocked_cells, prefer a "
            "budget-narrow next hint: either choose one exact "
            "`propagation`/`model_finder` route such as `find_model:n5`, or choose "
            "`focused_local_search`/one exact local route with `focus_cells` copied "
            "from branch_cells, blocked_cells, or best_partial hot cells. Broad "
            "unfocused `local_search` over multiple sizes/seeds is often too vague "
            "after propagation diagnostics.\n"
        )
    if mode == "tool_call":
        extra_constraints += (
            "- In tool_call mode, return exactly one JSON object with "
            "`kind: tool_call`. Allowed tools: `forward_saturation`, "
            "`proof_battery`, `goal_superposition`, `square_sandwich_chain`, "
            "`rowconst_certificates`, `certificates`, `grounding_derived`, "
            "`lemma_hint`, `lemma_chain`, and `false_model_search`. "
            "Allowed target: `goal`. `seed_terms` are "
            "used only by `forward_saturation` and must be Lean term strings "
            "using only the current goal variables and `◇`; omit or keep them "
            "short if unsure. For `lemma_hint`, include `equation` or `lemmas` "
            "with small bridge equations. For `lemma_chain`, include `lemmas`, "
            "a list of 2-5 helper equations. For `false_model_search`, include "
            "`template`, `sizes`, `seeds`, optional `routes`/`focus_cells`, and "
            "a fixed `budget`. `budget` should usually be 1-8 seconds.\n"
            "- If previous attempts show both `forward_saturation` and "
            "`goal_superposition` are stuck, do not cycle back to the same tools "
            "unless you have genuinely new parameters. Prefer `lemma_hint` with "
            "2-5 concrete bridge equations, or `lemma_chain` if the feedback asks "
            "for multiple helper equations.\n"
        )
    uncertain_contract = (
        "return your best h-argument hints inside the JSON `h_args` list."
        if mode == "hargs"
        else (
            "return your best intermediate equation inside the JSON `equation` field."
            if mode == "lemma_hint"
            else (
                "return your best named lemma chain inside the JSON `lemmas` list."
                if mode == "lemma_chain"
                else (
                    "return your best finite-model search hint as JSON."
                    if mode == "false_model_hint"
                    else (
                        "return your best mechanical tool call as JSON."
                        if mode == "tool_call"
                        else "return your best Lean tactic body inside the JSON `proof` string."
                    )
                )
            )
        )
    )
    role_intro = (
        "You are proposing finite countermodel search hints for a magma "
        "equational-theory problem. The binary operation is `◇`, not `*`.\n\n"
        if mode == "false_model_hint"
        else (
            "You are steering trusted mechanical proof tools for a magma "
            "equational-theory problem. The binary operation is `◇`, not `*`.\n\n"
            if mode == "tool_call"
            else (
            "You are a Lean 4 proof engineer for a magma equational-theory problem.\n"
            "The binary operation is `◇`, not `*`. Work inside an arbitrary `G : Type` "
            "with `[Magma G]` and a hypothesis `h` for the first equation.\n\n"
            )
        )
    )
    important_constraints = (
        "Important constraints:\n"
        "- Return ONLY one JSON object, no markdown and no commentary.\n"
        "- Do not write Lean proof text, tactics, imports, or a theorem.\n"
        "- Do not claim the verdict yourself; propose search controls for the mechanical side.\n"
        "- In false_model_hint mode, return only model-search instructions. "
        "Allowed templates include `local_search`, `model_finder`, "
        "`focused_local_search`, `existing_families`, `affine_mod_n`, and `quadratic_mod_n`. "
        "Use `sizes` or `carrier_size` for carrier sizes. Use `seeds` for "
        "local_search. Only after a previous attempt shows "
        "`untried_requested_routes`, you may copy exact strings from that list "
        "into `routes` to prioritize those searches. A full "
        "`counterexample_table` is allowed only if you "
        "are intentionally proposing a complete finite magma table. If previous "
        "attempts show failed routes, do not repeat them exactly; adapt the "
        "search plan to the remaining budget. If `best_near_misses` says H is "
        "satisfied but G still holds, prefer a G-breaking size/template; if it "
        "says G already fails but H has hotspot cells, prefer a narrower "
        "`focused_local_search` route with `focus_cells` aimed at those H hotspots.\n"
        "If `propagation_runs` reports branch_cells or blocked_cells, prefer a "
        "budget-narrow next hint: either choose one exact "
        "`propagation`/`model_finder` route such as `find_model:n5`, or choose "
        "`focused_local_search`/one exact local route with `focus_cells` copied "
        "from branch_cells, blocked_cells, or best_partial hot cells. Broad "
        "unfocused `local_search` over multiple sizes/seeds is often too vague "
        "after propagation diagnostics.\n"
        if mode == "false_model_hint"
        else (
            "Important constraints:\n"
            "- Return ONLY one JSON object, no markdown and no commentary.\n"
            "- Do not write Lean proof text, tactics, imports, or a theorem.\n"
            "- Do not claim the verdict yourself; choose a mechanical tool call.\n"
            "- Allowed tools: `proof_battery`, `forward_saturation`, "
            "`goal_superposition`, `square_sandwich_chain`, "
            "`rowconst_certificates`, `certificates`, `grounding_derived`, "
            "`lemma_hint`, and `lemma_chain`, plus false-side "
            "`false_model_search`; allowed target: `goal`.\n"
            "- Use `seed_terms` only for `forward_saturation`, and only for terms "
            "in scope after the goal variables are introduced.\n"
            "- Use `false_model_search` only when you are trying to produce a "
            "finite countermodel; include `template`, `sizes`, `seeds`, and "
            "optional `routes`, `focus_cells`, `freeze_cells`, or `bias_cells`.\n"
            "- When the tool-selection advice shows `llm_only_actions`, fill in "
            "one of those templates with concrete equations instead of repeating "
            "a failed ranked mechanical call.\n"
            if mode == "tool_call"
            else (
            "Important constraints:\n"
            "- Return ONLY one JSON object, no markdown and no commentary.\n"
            "- Do not include imports, `def submission`, or `intro G _ h`.\n"
            "- Only use variables introduced by the current goal. If `h` has extra "
            "variables, instantiate them with concrete terms made from the introduced "
            "goal variables; do not write bare unused names like `z` unless `z` was introduced.\n"
            "- Do not use unavailable tactics such as `aesop`, `omega`, `linarith`, or `tauto`.\n"
            "- Avoid bare `grind`; it often proves via disallowed axioms in LLM-written proofs. "
            "Prefer explicit named equalities and `calc`.\n"
            "- In a `calc` or `.trans` chain, adjacent terms must match exactly. "
            "If `f : A = B` and `g : C = D`, then `f.trans g.symm` works only when "
            "`B` and `D` are syntactically the same Lean term. If they differ, insert "
            "more h-facts until both sides reach a common reduct.\n"
            "- Do not use `sorry`, `admit`, axioms, unsafe code, macros, or declarations.\n"
            "- Avoid `simp [lemma]` / `simpa [lemma]`; this can introduce disallowed axioms. "
            "Prefer explicit `calc`, `.trans`, `.symm`, `rw`, or `simpa using hfact`.\n"
            f"{extra_constraints}"
            "- It is okay if indentation is imperfect; the sidecar will clean obvious scaffolding.\n"
            )
        )
    )

    return (
        "CRITICAL OUTPUT CONTRACT: your entire response must be exactly one JSON object.\n"
        "It must start with `{` and end with `}`. Do not include analysis, prose, "
        f"markdown, code fences, or chain-of-thought. If you are uncertain, still {uncertain_contract}\n\n"
        f"{role_intro}"
        f"{context}\n"
        f"{standard_helper_block}"
        f"{square_chain_block}"
        f"{tool_registry_block}"
        f"{tool_advice_block}"
        f"{fact_menu}"
        f"{wrapper}\n"
        f"{fewshot_block}\n"
        f"{mode_instruction}\n\n"
        f"{important_constraints}\n"
        f"{attempts}\n\n"
        "JSON schema:\n"
        f"{schema}\n"
    )


def strip_code_fences(text: str) -> str:
    text = text.strip()
    if text.startswith("```"):
        text = re.sub(r"^```[A-Za-z0-9_-]*\s*", "", text)
        text = re.sub(r"\s*```$", "", text)
    return text.strip()


def light_preclean(raw: str) -> str:
    """Fix small, common LLM scaffold mistakes before the existing cleaner runs."""
    text = strip_code_fences(raw).replace("*", "◇").replace("\r\n", "\n")
    text = re.sub(r"^\s*by\s*\n", "", text)
    # Common theorem-style answer: `intros h x y; ...`. The wrapper already has h.
    text = re.sub(r"^\s*intros?\s+h\b\s*", "intro ", text)
    # Split compact semicolon chains at tactic/term keywords. This salvages many
    # one-line "have; have; calc" answers without trying to parse Lean.
    text = re.sub(
        r";\s*(?=(have|calc|exact|apply|grind|rw|simp|intro|intros|refine|show)\b)",
        "\n",
        text,
    )
    return text.strip()


def extract_body(llm_text: str) -> tuple[str, dict[str, Any]]:
    data = solver_core._extract_json(llm_text)
    if isinstance(data, dict):
        body = (
            data.get("proof")
            or data.get("body")
            or data.get("code")
            or data.get("lean")
            or ""
        )
        return str(body), data
    # Salvage a fenced Lean block if a model ignored the JSON envelope but did
    # produce code. Do not feed plain English reasoning to Lean; that creates
    # noisy errors and teaches the repair loop the wrong lesson.
    fence = re.search(r"```(?:lean|Lean|LEAN)?\s*(.*?)```", llm_text, re.DOTALL)
    if fence:
        return fence.group(1).strip(), {"kind": "fenced_lean_no_json"}
    codeish_lines = []
    for line in llm_text.splitlines():
        stripped = line.strip()
        if re.match(
            r"^(intro|intros|have|calc|exact|apply|rw|simp|grind|show|refine)\b",
            stripped,
        ):
            codeish_lines.append(stripped)
    if codeish_lines:
        return "\n".join(codeish_lines), {"kind": "codeish_no_json"}
    return "", {
        "kind": "protocol_error",
        "error": "no JSON object or Lean code block found",
        "raw_excerpt": llm_text[:1200],
    }


def extract_tool_call(llm_text: str) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    data = solver_core._extract_json(llm_text)
    if not isinstance(data, dict):
        return None, {
            "kind": "protocol_error",
            "error": "no JSON object with tool_call found",
            "raw_excerpt": llm_text[:1200],
        }
    if data.get("kind") != "tool_call" and not data.get("tool"):
        return None, {
            "kind": "protocol_error",
            "error": "JSON must have `kind: tool_call` and a `tool` field",
            "raw": data,
        }
    seed_terms = data.get("seed_terms") or data.get("terms") or data.get("seeds") or []
    if isinstance(seed_terms, str):
        seed_terms = [seed_terms]
    if not isinstance(seed_terms, list):
        seed_terms = []
    call = {
        "kind": "tool_call",
        "tool": normalize_tool_name(str(data.get("tool") or "").strip()),
        "target": str(data.get("target") or "goal").strip() or "goal",
        "seed_terms": [strip_code_fences(str(term)).strip().strip("`").replace("*", "◇") for term in seed_terms],
        "budget": float(data.get("budget") or data.get("time_budget") or data.get("budget_seconds") or 3.0),
        "why": str(data.get("why") or data.get("rationale") or "")[:500],
        "raw": data,
    }
    return call, data


def _clean_arg_term(term: Any) -> str:
    text = str(term).strip().strip("`").replace("*", "◇")
    if "◇" in text and not (text.startswith("(") and text.endswith(")")):
        text = f"({text})"
    return text


def extract_h_arg_hints(llm_text: str, expected_nargs: int) -> tuple[list[tuple[str, ...]], dict[str, Any]]:
    data = solver_core._extract_json(llm_text)
    if not isinstance(data, dict):
        return [], {
            "kind": "protocol_error",
            "error": "no JSON object with h_args found",
            "raw_excerpt": llm_text[:1200],
        }
    raw_args = data.get("h_args") or data.get("args") or data.get("instantiations") or []
    if not isinstance(raw_args, list):
        return [], {"kind": "protocol_error", "error": "`h_args` must be a list", "raw": data}
    if len(raw_args) == expected_nargs and all(not isinstance(item, list) for item in raw_args):
        raw_args = [raw_args]
    out: list[tuple[str, ...]] = []
    for row in raw_args:
        if not isinstance(row, list) or len(row) != expected_nargs:
            continue
        tup = tuple(_clean_arg_term(item) for item in row)
        if all(tup):
            out.append(tup)
    return _dedupe_args(out), data


def parse_arg_rows(raw_args: Any, expected_nargs: int) -> list[tuple[str, ...]]:
    if not isinstance(raw_args, list):
        return []
    if len(raw_args) == expected_nargs and all(not isinstance(item, list) for item in raw_args):
        raw_args = [raw_args]
    out: list[tuple[str, ...]] = []
    for row in raw_args:
        if not isinstance(row, list) or len(row) != expected_nargs:
            continue
        tup = tuple(_clean_arg_term(item) for item in row)
        if all(tup):
            out.append(tup)
    return _dedupe_args(out)


def extract_equation_text(raw: Any) -> str:
    text = strip_code_fences(str(raw or "")).strip().strip("`").replace("*", "◇")
    if not text:
        return ""
    text = re.sub(r"^\s*have\s+\w+\s*:\s*", "", text)
    text = re.sub(r"^\s*lemma\s+\w+\s*:\s*", "", text)
    text = re.sub(r"^\s*theorem\s+\w+\s*:\s*", "", text)
    text = re.sub(r"^\s*∀\s+[^,]+,\s*", "", text)
    return text.strip()


def balance_equation_parentheses(text: str) -> str:
    """Repair the common LLM typo of dropping final close-parens on one side."""
    if "=" not in text:
        return text
    lhs, rhs = text.split("=", 1)

    def balance_side(side: str) -> str:
        stripped = side.strip()
        opens = stripped.count("(")
        closes = stripped.count(")")
        if opens > closes:
            stripped += ")" * (opens - closes)
        elif closes > opens:
            stripped = "(" * (closes - opens) + stripped
        return stripped

    return f"{balance_side(lhs)} = {balance_side(rhs)}"


def _parse_lemma_hint_data(data: dict[str, Any], *, h_nargs: int) -> dict[str, Any] | None:
    equation_text = (
        data.get("equation")
        or data.get("lemma_equation")
        or data.get("lemma")
        or data.get("statement")
        or ""
    )
    equation_text = extract_equation_text(equation_text)
    try:
        lemma_eq = solver_core.parse_equation(solver_core.normalize(equation_text))
    except Exception as exc:  # noqa: BLE001
        repaired_text = balance_equation_parentheses(equation_text)
        if repaired_text != equation_text:
            try:
                lemma_eq = solver_core.parse_equation(solver_core.normalize(repaired_text))
                data["syntax_repair"] = {
                    "kind": "balanced_parentheses",
                    "before": equation_text,
                    "after": repaired_text,
                }
                equation_text = repaired_text
            except Exception as repaired_exc:  # noqa: BLE001
                data["parse_error"] = f"{type(exc).__name__}: {exc}"
                data["repair_parse_error"] = f"{type(repaired_exc).__name__}: {repaired_exc}"
                data["parsed_equation_text"] = equation_text
                data["repaired_equation_text"] = repaired_text
                return None
        else:
            data["parse_error"] = f"{type(exc).__name__}: {exc}"
            data["parsed_equation_text"] = equation_text
            return None

    seed_h_args = parse_arg_rows(
        data.get("seed_h_args") or data.get("h_args") or data.get("instantiations") or [],
        h_nargs,
    )
    use_args = parse_arg_rows(
        data.get("use_args") or data.get("lemma_args") or [],
        len(lemma_eq["variables"]),
    )
    hint = {
        "eq": lemma_eq,
        "seed_h_args": seed_h_args,
        "use_args": use_args,
        "equation_text": lemma_eq["text"],
    }
    if data.get("syntax_repair"):
        hint["syntax_repair"] = data["syntax_repair"]
    return hint


def extract_lemma_hints(
    llm_text: str,
    *,
    h_nargs: int,
    max_hints: int = 8,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    data = solver_core._extract_json(llm_text)
    if not isinstance(data, dict):
        return [], {
            "kind": "protocol_error",
            "error": "no JSON object with lemma equation found",
            "raw_excerpt": llm_text[:1200],
        }

    raw_candidates: list[Any] = []
    for key in ("lemma_hints", "lemmas", "candidates", "equations"):
        value = data.get(key)
        if isinstance(value, list):
            raw_candidates.extend(value)
    if any(data.get(key) for key in ("equation", "lemma_equation", "lemma", "statement")):
        raw_candidates.insert(0, data)

    parsed: list[dict[str, Any]] = []
    seen: set[str] = set()
    parse_errors: list[Any] = []
    for raw in raw_candidates[: max_hints * 2]:
        if isinstance(raw, str):
            item = {"equation": raw}
        elif isinstance(raw, dict):
            item = dict(raw)
        else:
            continue
        hint = _parse_lemma_hint_data(item, h_nargs=h_nargs)
        if hint is None:
            parse_errors.append(item)
            continue
        if hint["equation_text"] in seen:
            continue
        seen.add(hint["equation_text"])
        parsed.append(hint)
        if len(parsed) >= max_hints:
            break
    if parse_errors:
        data["candidate_parse_errors"] = parse_errors[:3]
    return parsed, data


def extract_lemma_hint(
    llm_text: str,
    *,
    h_nargs: int,
) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    hints, payload = extract_lemma_hints(llm_text, h_nargs=h_nargs, max_hints=1)
    return (hints[0] if hints else None), payload


def extract_lemma_chain_hint(
    llm_text: str,
    *,
    h_nargs: int,
    max_hints: int = 8,
) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    data = solver_core._extract_json(llm_text)
    if not isinstance(data, dict):
        return None, {
            "kind": "protocol_error",
            "error": "no JSON object with a lemma chain found",
            "raw_excerpt": llm_text[:1200],
        }

    raw_items: list[Any] = []
    for key in ("lemmas", "lemma_chain", "chain", "steps", "equations"):
        value = data.get(key)
        if isinstance(value, list):
            raw_items.extend(value)
    if any(data.get(key) for key in ("equation", "lemma_equation", "lemma", "statement")):
        raw_items.insert(0, data)

    parsed: list[dict[str, Any]] = []
    parse_errors: list[Any] = []
    seen: set[str] = set()
    for raw in raw_items[: max_hints * 2]:
        if isinstance(raw, str):
            item = {"equation": raw}
        elif isinstance(raw, dict):
            item = dict(raw)
        else:
            continue
        hint = _parse_lemma_hint_data(item, h_nargs=h_nargs)
        if hint is None:
            parse_errors.append(item)
            continue
        equation = hint["equation_text"]
        if equation in seen:
            continue
        seen.add(equation)
        kind = _lemma_chain_helper_kind(hint["eq"])
        lemma_eq = _canonical_helper_eq(kind, hint["eq"]) if kind else hint["eq"]
        parsed.append({
            "name": item.get("name") or item.get("lemma_name"),
            "eq": lemma_eq,
            "equation_text": lemma_eq["text"],
            "original_equation_text": equation,
            "kind": kind,
            "seed_h_args": hint.get("seed_h_args") or [],
            "use_args": hint.get("use_args") or [],
            "syntax_repair": hint.get("syntax_repair"),
        })
        if len(parsed) >= max_hints:
            break

    if parse_errors:
        data["candidate_parse_errors"] = parse_errors[:3]
    if not parsed:
        return None, data
    return {
        "kind": "lemma_chain",
        "lemmas": parsed,
        "witness_term": extract_equation_text(data.get("witness_term") or ""),
    }, data


def _int_list(value: Any, *, default: list[int], min_value: int = 0, max_value: int = 50) -> list[int]:
    raw = value
    if raw is None:
        return list(default)
    if isinstance(raw, int):
        raw = [raw]
    if not isinstance(raw, list):
        return list(default)
    out: list[int] = []
    for item in raw:
        try:
            number = int(item)
        except Exception:  # noqa: BLE001
            continue
        if min_value <= number <= max_value and number not in out:
            out.append(number)
    return out or list(default)


def _cell_from_value(value: Any) -> tuple[int, int] | None:
    raw = value.get("cell") if isinstance(value, dict) else value
    if not isinstance(raw, list) or len(raw) != 2:
        return None
    try:
        i = int(raw[0])
        j = int(raw[1])
    except Exception:  # noqa: BLE001
        return None
    if i < 0 or j < 0 or i > 64 or j > 64:
        return None
    return i, j


def _cell_list(value: Any, *, max_cells: int = 24) -> list[list[int]]:
    if not isinstance(value, list):
        return []
    cells: list[list[int]] = []
    seen: set[tuple[int, int]] = set()
    for item in value:
        cell = _cell_from_value(item)
        if cell is None or cell in seen:
            continue
        seen.add(cell)
        cells.append([cell[0], cell[1]])
        if len(cells) >= max_cells:
            break
    return cells


def _cell_value_list(value: Any, *, max_items: int = 24) -> list[dict[str, Any]]:
    if not isinstance(value, list):
        return []
    rows: list[dict[str, Any]] = []
    seen: set[tuple[int, int, tuple[int, ...]]] = set()
    for item in value:
        if not isinstance(item, dict):
            continue
        cell = _cell_from_value(item)
        if cell is None:
            continue
        raw_values = item.get("values")
        if raw_values is None and item.get("value") is not None:
            raw_values = [item.get("value")]
        if isinstance(raw_values, int):
            raw_values = [raw_values]
        if not isinstance(raw_values, list):
            raw_values = []
        values: list[int] = []
        for raw in raw_values:
            try:
                val = int(raw)
            except Exception:  # noqa: BLE001
                continue
            if 0 <= val <= 64 and val not in values:
                values.append(val)
        key = (cell[0], cell[1], tuple(values))
        if key in seen:
            continue
        seen.add(key)
        rows.append({"cell": [cell[0], cell[1]], "values": values})
        if len(rows) >= max_items:
            break
    return rows


def extract_false_model_hints(
    llm_text: str,
    *,
    max_hints: int = 6,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    data = solver_core._extract_json(llm_text)
    if not isinstance(data, dict):
        return [], {
            "kind": "protocol_error",
            "error": "no JSON object with a false model hint found",
            "raw_excerpt": llm_text[:1200],
        }

    raw_hints: list[Any] = []
    for key in ("hints", "model_hints", "candidates", "false_model_hints"):
        value = data.get(key)
        if isinstance(value, list):
            raw_hints.extend(value)
    if data.get("kind") == "false_model_hint" or any(
        key in data
        for key in ("carrier_size", "sizes", "template", "counterexample_table", "table", "operation")
    ):
        raw_hints.insert(0, data)

    hints: list[dict[str, Any]] = []
    for raw in raw_hints[: max_hints * 2]:
        if not isinstance(raw, dict):
            continue
        item = dict(raw)
        table = item.get("counterexample_table") or item.get("table")
        sizes = _int_list(
            item.get("sizes") or item.get("carrier_sizes") or item.get("carrier_size"),
            default=[5, 6],
            min_value=2,
            max_value=12,
        )
        seeds = _int_list(item.get("seeds") or item.get("seed"), default=[0], min_value=0, max_value=10_000)
        template = str(item.get("template") or item.get("operation") or "local_search").strip().lower()
        hint = {
            "kind": "false_model_hint",
            "template": template,
            "sizes": sizes,
            "seeds": seeds[:8],
            "routes": [
                str(route)
                for route in (item.get("routes") or item.get("try_routes") or item.get("priority_routes") or [])
                if isinstance(route, str)
            ][:16],
            "focus_cells": _cell_list(
                item.get("focus_cells")
                or item.get("target_cells")
                or item.get("h_hot_cells")
                or item.get("cells")
            ),
            "freeze_cells": _cell_value_list(item.get("freeze_cells") or item.get("frozen_cells")),
            "bias_cells": _cell_value_list(item.get("bias_cells") or item.get("value_biases")),
            "time_budget": float(item.get("time_budget") or item.get("budget_seconds") or 0.0),
            "constraints": item.get("constraints") if isinstance(item.get("constraints"), list) else [],
            "separate_goal_at": item.get("separate_goal_at") if isinstance(item.get("separate_goal_at"), dict) else None,
            "rationale": str(item.get("rationale") or "")[:500],
            "table": table,
        }
        hints.append(hint)
        if len(hints) >= max_hints:
            break
    return hints, data


def rank_lemma_hints(hints: list[dict[str, Any]], g_eq: dict[str, Any]) -> list[dict[str, Any]]:
    goal_terms = set(
        solver_core.goal_term_pool(g_eq, max_terms=24)
        + _small_goal_compounds(g_eq, limit=24)
        + g_eq["variables"]
    )
    goal_text = g_eq["text"]

    def score(hint: dict[str, Any]) -> tuple[int, int, str]:
        eq = hint["eq"]
        lhs = solver_core.term_to_str(eq["lhs"])
        rhs = solver_core.term_to_str(eq["rhs"])
        total_size = solver_core.term_size(eq["lhs"]) + solver_core.term_size(eq["rhs"])
        value = 0
        if standard_lemma_kind(eq):
            value += 80
        if lhs in goal_terms or rhs in goal_terms:
            value += 35
        if lhs in goal_text or rhs in goal_text:
            value += 20
        if len(eq["variables"]) <= 3:
            value += 10
        if total_size <= 8:
            value += 8
        elif total_size <= 14:
            value += 3
        value -= max(0, total_size - 14)
        return (-value, total_size, hint["equation_text"])

    ranked = sorted(hints, key=score)
    for idx, hint in enumerate(ranked, 1):
        hint["rank"] = idx
        hint["rank_score"] = -score(hint)[0]
    return ranked


def candidate_from_args(args: argparse.Namespace) -> tuple[str | None, dict[str, Any]]:
    if args.candidate_proof_file:
        return args.candidate_proof_file.read_text(encoding="utf-8"), {"kind": "candidate_file"}
    if args.candidate_json_file:
        text = args.candidate_json_file.read_text(encoding="utf-8")
        if args.mode in ("lemma_hint", "lemma_chain", "hargs", "false_model_hint", "tool_call"):
            return text, {"kind": "candidate_json_file", "mode": args.mode}
        body, meta = extract_body(text)
        return body, meta
    if args.candidate_proof:
        return args.candidate_proof, {"kind": "candidate_arg"}
    return None, {}


def clean_body(raw_body: str, goal_vars: list[str]) -> str:
    return solver_core.clean_llm_proof_body(light_preclean(raw_body), goal_vars)


def local_rejection(cleaned_body: str) -> tuple[str, str] | None:
    """Reject uninformative LLM bodies before spending Lean time.

    A bare `grind` attempt gives poor learning signal and frequently verifies
    only through disallowed axioms. Bodies with named h-instantiations are still
    passed through Lean, because `grind` can be useful once it has real facts.
    """
    meaningful = [
        line.strip()
        for line in cleaned_body.splitlines()
        if line.strip() and not line.strip().startswith("--")
    ]
    non_intro = [
        line
        for line in meaningful
        if not re.match(r"^(intro|intros)\b", line)
    ]
    if non_intro == ["grind"]:
        return (
            "BARE_GRIND",
            "Local rejection: the body only introduces variables and calls "
            "`grind`. Instantiate `h` into named facts first, then connect "
            "the target with `calc`, `simpa using fact`, `.trans`, `.symm`, "
            "or `rw` steps.",
        )
    return None


def verify_body(
    *,
    problem: dict[str, Any],
    body: str,
    lean_timeout_seconds: int,
    artifact_dir: Path,
) -> tuple[dict[str, Any], str]:
    code = solver_core.lean_true(body)
    answer = json.dumps({"verdict": "true", "code": code})
    cfg = JudgeConfig(
        artifact_dir=artifact_dir,
        lean_timeout_seconds=lean_timeout_seconds,
        max_code_length=100_000,
        max_false_cert_bytes=20_000,
    )
    try:
        return verify_answer(problem, answer, config=cfg), code
    except Exception as exc:  # noqa: BLE001
        return {
            "status": "verifier_error",
            "error_code": "VERIFY_EXCEPTION",
            "message": f"Verifier raised {type(exc).__name__}: {exc}",
            "verdict": "true",
        }, code


def _parse_tool_seed_terms(
    seed_terms: list[str],
    g_eq: dict[str, Any],
) -> tuple[list[Any], list[dict[str, str]]]:
    variables = set(g_eq["variables"] or ["x"])
    parsed: list[Any] = []
    invalid: list[dict[str, str]] = []
    seen: set[str] = set()
    for raw in seed_terms:
        text = str(raw or "").strip().strip("`").replace("*", "◇")
        if not text:
            continue
        try:
            term = solver_core.parse_term(text, variables)
        except Exception as exc:  # noqa: BLE001
            invalid.append({"term": text, "error": f"{type(exc).__name__}: {exc}"})
            continue
        rendered = solver_core.term_to_str(term)
        if rendered not in seen:
            seen.add(rendered)
            parsed.append(term)
    return parsed, invalid


def _tool_sat_key(term: Any) -> str:
    try:
        return solver_core._sat_key(term)
    except Exception:  # noqa: BLE001
        return solver_core.term_to_str(term)


def _tool_sat_arg(term: Any) -> str:
    try:
        return solver_core._sat_arg(term)
    except Exception:  # noqa: BLE001
        return term[1] if term[0] == "var" else f"({solver_core.term_to_str(term)})"


def _saturation_combos_with_seed_terms(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    *,
    seed_terms: list[Any],
    depth: int,
    pool_cap: int,
    slots: int,
) -> tuple[list[tuple[Any, ...]], list[Any]]:
    hv = h_eq["variables"]
    gv = g_eq["variables"] or ["x"]
    pad = ("var", gv[0])
    pool_set = solver_core._sat_subterms(g_eq["lhs"]) | solver_core._sat_subterms(g_eq["rhs"])
    for term in seed_terms:
        pool_set |= solver_core._sat_subterms(term)

    def order(term: Any) -> tuple[int, str]:
        return (solver_core.term_size(term), _tool_sat_key(term))

    pool = sorted(pool_set, key=order)
    combos: list[tuple[Any, ...]] = []
    seen: set[tuple[str, ...]] = set()
    for _round in range(depth):
        new_terms = set()
        round_combos: list[tuple[Any, ...]] = []
        for term in pool:
            for slot in range(min(slots, len(hv))):
                combo = [pad] * len(hv)
                combo[slot] = term
                round_combos.append(tuple(combo))
        round_combos.append(tuple([pad] * len(hv)))
        for combo in round_combos:
            key = tuple(_tool_sat_key(term) for term in combo)
            if key in seen:
                continue
            seen.add(key)
            combos.append(combo)
            subst = {hv[i]: combo[i] for i in range(len(hv))}
            new_terms |= solver_core._sat_subterms(solver_core._sat_inst(h_eq["rhs"], subst))
        pool = sorted(set(pool) | new_terms, key=order)[:pool_cap]
    return combos, pool


def _saturation_body_from_combos(g_eq: dict[str, Any], combos: list[tuple[Any, ...]]) -> str:
    lines: list[str] = []
    if g_eq["variables"]:
        lines.append("intro " + " ".join(g_eq["variables"]))
    for i, combo in enumerate(combos, 1):
        lines.append(f"have c{i} := h " + " ".join(_tool_sat_arg(term) for term in combo))
    lines.append("grind")
    return "\n".join(lines)


def _h_args_preview(h_eq: dict[str, Any], combos: list[tuple[Any, ...]], *, limit: int = 16) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for combo in combos[:limit]:
        args = tuple(_tool_sat_arg(term) for term in combo)
        lhs, rhs = render_h_type(h_eq, args)
        out.append({"args": list(args), "lhs": lhs, "rhs": rhs})
    return out


def run_forward_saturation_tool(
    *,
    args: argparse.Namespace,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    tool_call: dict[str, Any],
) -> tuple[dict[str, Any], str, str]:
    started = time.time()
    budget = max(0.25, min(float(tool_call.get("budget") or 3.0), 12.0))
    deadline = started + budget
    parsed_seeds, invalid_seeds = _parse_tool_seed_terms(tool_call.get("seed_terms") or [], g_eq)
    configs = getattr(solver_core, "_SAT_CONFIGS", ((2, 10, 1, 16), (2, 10, 2, 24), (3, 14, 2, 40), (3, 14, 3, 48)))
    max_bodies = int(tool_call.get("max_bodies") or len(configs))
    body_seen: set[str] = set()
    trials: list[dict[str, Any]] = []
    best_combos: list[tuple[Any, ...]] = []
    best_pool: list[Any] = []
    best_config: tuple[int, int, int, int] | None = None
    last_body = ""
    last_code = ""

    for depth, pool_cap, slots, have_cap in list(configs)[:max_bodies]:
        if time.time() > deadline and trials:
            break
        combos, pool = _saturation_combos_with_seed_terms(
            h_eq,
            g_eq,
            seed_terms=parsed_seeds,
            depth=depth,
            pool_cap=pool_cap,
            slots=slots,
        )
        combos = combos[:have_cap]
        combo_args = [
            tuple(_tool_sat_arg(term) for term in combo)
            for combo in combos
        ]
        graph_body = h_graph_body(
            h_eq,
            g_eq,
            max(int(getattr(args, "max_h_facts", 0) or 0), have_cap, len(combo_args)),
            extra_args=combo_args,
            congruence_depth=int(getattr(args, "congruence_depth", 0) or 0),
            max_congruence_facts=int(getattr(args, "max_congruence_facts", 240) or 240),
        )
        body = graph_body or _saturation_body_from_combos(g_eq, combos)
        consumer = "h_fact_graph" if graph_body is not None else "grind"
        if body in body_seen:
            continue
        body_seen.add(body)
        last_body = clean_body(body, g_eq["variables"])
        remaining = max(0.25, deadline - time.time())
        if graph_body is not None:
            per_attempt_timeout = max(15, int(args.lean_timeout_seconds))
            timeout_source = "stable_graph_proof"
        else:
            per_attempt_timeout = max(1, min(int(args.lean_timeout_seconds), int(math.ceil(remaining))))
            timeout_source = "remaining_tool_budget"
        t0 = time.time()
        result, lean_code = verify_body(
            problem=problem,
            body=last_body,
            lean_timeout_seconds=per_attempt_timeout,
            artifact_dir=args.artifact_dir,
        )
        last_code = lean_code
        feedback = feedback_from_result(
            result,
            max_lines=min(args.max_feedback_lines, 18),
            max_chars=min(args.max_feedback_chars, 1800),
        )
        trial = {
            "config": {
                "depth": depth,
                "pool_cap": pool_cap,
                "slots": slots,
                "have_cap": have_cap,
            },
            "status": result.get("status"),
            "error_code": result.get("error_code"),
            "elapsed": round(time.time() - t0, 3),
            "lean_timeout_seconds": per_attempt_timeout,
            "consumer": consumer,
            "graph_path_found": graph_body is not None,
            "fact_count": len(combos),
            "pool_size": len(pool),
            "verification_timeout_source": timeout_source,
            "feedback": feedback,
        }
        trials.append(trial)
        if len(combos) > len(best_combos):
            best_combos = combos
            best_pool = pool
            best_config = (depth, pool_cap, slots, have_cap)
        if result.get("status") == "accepted":
            module_state = {
                "kind": "forward_saturation_tool",
                "tool": "forward_saturation",
                "status": "accepted",
                "target": "goal",
                "seed_terms": [solver_core.term_to_str(term) for term in parsed_seeds],
                "invalid_seed_terms": invalid_seeds,
                "budget_seconds": budget,
                "elapsed": round(time.time() - started, 3),
                "attempt_count": len(trials),
                "accepted_count": 1,
                "trials": trials,
                "winning_config": trial["config"],
            }
            accepted = dict(result)
            accepted["module_state"] = module_state
            return accepted, last_body, last_code

    generated_terms = _unique([solver_core.term_to_str(term) for term in best_pool])
    generated_h_args = _h_args_preview(h_eq, best_combos, limit=20)
    seed_h_arg_rows = [
        row["args"]
        for row in generated_h_args[:8]
        if isinstance(row.get("args"), list)
    ]
    need_hint = {
        "need_hint": "choose better seed_terms for forward_saturation or switch to a lemma/tool strategy",
        "goal_left": solver_core.term_to_str(g_eq["lhs"]),
        "goal_right": solver_core.term_to_str(g_eq["rhs"]),
        "suggested_seed_terms": generated_terms[:16],
        "current_seed_terms": [solver_core.term_to_str(term) for term in parsed_seeds],
        "invalid_seed_terms": invalid_seeds,
        "next_tool_call_shape": {
            "kind": "tool_call",
            "tool": "forward_saturation",
            "target": "goal",
            "seed_terms": generated_terms[:6],
            "budget": budget,
        },
        "llm_tool_call_templates": [
            {
                "kind": "tool_call",
                "tool": "lemma_hint",
                "target": "goal",
                "lemmas": [
                    "<bridge equation connecting goal_left to a generated term>",
                    "<bridge equation connecting a generated term to goal_right>",
                ],
                "seed_h_args": seed_h_arg_rows,
                "seed_h_args_note": (
                    "These are concrete h-instance rows from the failed saturation "
                    "run. Keep or edit the rows that help prove the bridge lemma."
                ),
                "why": (
                    "forward_saturation generated h-instances but no equality path; "
                    "suggest a small lemma/midpoint for the mechanical lemma consumer"
                ),
                "requires_llm_content": True,
            }
        ],
    }
    module_state = {
        "kind": "forward_saturation_tool",
        "tool": "forward_saturation",
        "status": "stuck" if trials else "no_trials",
        "target": "goal",
        "seed_terms": [solver_core.term_to_str(term) for term in parsed_seeds],
        "invalid_seed_terms": invalid_seeds,
        "budget_seconds": budget,
        "elapsed": round(time.time() - started, 3),
        "attempt_count": len(trials),
        "accepted_count": 0,
        "trials": trials,
        "best_config": {
            "depth": best_config[0],
            "pool_cap": best_config[1],
            "slots": best_config[2],
            "have_cap": best_config[3],
        } if best_config else None,
        "generated_terms": generated_terms[:24],
        "generated_h_args": generated_h_args,
        "need_hint": need_hint,
    }
    result = {
        "status": "incorrect",
        "error_code": "TOOL_FORWARD_SATURATION_STUCK",
        "message": (
            "forward_saturation did not produce an accepted proof. The module "
            "state lists generated terms/h-instantiations and asks for better "
            "seed_terms or a different next tool strategy."
        ),
        "verdict": "true",
        "module_state": module_state,
    }
    return result, last_body, last_code


def _tool_bool(raw: dict[str, Any], key: str, default: bool) -> bool:
    value = raw.get(key)
    if value is None:
        return default
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return bool(value)
    if isinstance(value, str):
        return value.strip().lower() not in {"0", "false", "no", "off"}
    return default


def _first_line_matching(text: str, prefixes: tuple[str, ...]) -> str | None:
    for line in text.splitlines():
        stripped = line.strip()
        if any(stripped.startswith(prefix) for prefix in prefixes):
            return stripped[:500]
    return None


def _battery_arg_layers(h_eq: dict[str, Any], g_eq: dict[str, Any]) -> list[dict[str, Any]]:
    """Return the old battery's h-argument layers without the final grind."""
    nargs = len(h_eq.get("variables") or [])
    if nargs <= 0:
        return []
    pad = (g_eq.get("variables") or ["x"])[0]
    terms = solver_core.goal_term_pool(g_eq)
    compound_terms = [term for term in terms if "◇" in term]
    diag = tuple([pad] * nargs)

    def slot(index: int, term_list: list[str]) -> list[tuple[str, ...]]:
        out: list[tuple[str, ...]] = []
        for term in term_list:
            args = [pad] * nargs
            if index < nargs:
                args[index] = term
            out.append(tuple(args))
        return out

    def dedup(rows: list[tuple[str, ...]]) -> list[tuple[str, ...]]:
        seen: set[tuple[str, ...]] = set()
        out: list[tuple[str, ...]] = []
        for row in rows:
            if row not in seen:
                seen.add(row)
                out.append(row)
        return out

    layers: list[dict[str, Any]] = [
        {"name": "diag", "args": [diag]},
    ]
    slot0 = dedup([diag] + slot(0, terms))
    layers.append({"name": "slot0_terms", "args": slot0})
    slot1 = dedup(slot0 + slot(1, compound_terms))
    layers.append({"name": "slot1_compounds", "args": slot1})
    if nargs >= 3:
        slot2 = dedup(slot1 + slot(2, compound_terms))
        layers.append({"name": "slot2_compounds", "args": slot2})
    pool = dedup(list(solver_core.instantiation_pool(h_eq, g_eq)))
    if pool:
        layers.append({"name": "instantiation_pool", "args": pool})
    return layers


def run_proof_battery_tool(
    *,
    args: argparse.Namespace,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    tool_call: dict[str, Any],
) -> tuple[dict[str, Any], str, str]:
    started = time.time()
    raw = _as_dict(tool_call.get("raw"))
    budget = max(1.0, min(float(tool_call.get("budget") or 18.0), 45.0))
    max_candidates = max(1, min(int(raw.get("max_candidates") or raw.get("candidates") or 5), 12))
    include_aux = _tool_bool(raw, "include_aux", True)
    include_graph = _tool_bool(raw, "include_graph", True)
    max_graph_candidates = max(0, min(int(raw.get("max_graph_candidates") or raw.get("graph_candidates") or 3), 8))
    try:
        implied_aux = solver_core.implied_aux_lemmas(h_eq) if include_aux and h_eq.get("free") else []
    except Exception as exc:  # noqa: BLE001
        implied_aux = []
        aux_error = f"{type(exc).__name__}: {exc}"
    else:
        aux_error = None
    verify_timeout = max(
        15,
        min(
            int(args.lean_timeout_seconds),
            int(math.ceil(float(raw.get("verify_timeout_seconds") or raw.get("verify_timeout") or max(15.0, budget)))),
        ),
    )
    attempts: list[dict[str, Any]] = []
    graph_layers_considered: list[dict[str, Any]] = []
    if include_graph and max_graph_candidates > 0:
        for layer in _battery_arg_layers(h_eq, g_eq):
            if len(graph_layers_considered) >= max_graph_candidates:
                break
            layer_name = str(layer["name"])
            layer_args = list(layer["args"])
            graph_layers_considered.append({
                "name": layer_name,
                "arg_count": len(layer_args),
            })
            graph_body = h_graph_body(
                h_eq,
                g_eq,
                0,
                extra_args=layer_args,
                congruence_depth=int(raw.get("graph_congruence_depth") or raw.get("congruence_depth") or 0),
                max_congruence_facts=int(raw.get("max_congruence_facts") or 240),
            )
            if graph_body is None:
                continue
            attempt = _verified_body_attempt(
                problem=problem,
                body=graph_body,
                source=f"tool_proof_battery_graph_{layer_name}",
                lean_timeout_seconds=max(15, int(args.lean_timeout_seconds)),
                artifact_dir=args.artifact_dir,
                max_feedback_lines=args.max_feedback_lines,
                max_feedback_chars=args.max_feedback_chars,
                clean=True,
            )
            attempts.append(attempt)
            if attempt.get("status") == "accepted":
                base_state = _module_state_from_attempts(
                    module="proof_battery",
                    budget=budget,
                    attempts=attempts,
                )
                module_state = {
                    **base_state,
                    "kind": "proof_battery_tool",
                    "tool": "proof_battery",
                    "target": "goal",
                    "elapsed": round(time.time() - started, 3),
                    "verify_timeout_seconds": verify_timeout,
                    "max_candidates": max_candidates,
                    "include_aux": include_aux,
                    "include_graph": include_graph,
                    "max_graph_candidates": max_graph_candidates,
                    "graph_layers_considered": graph_layers_considered,
                    "winning_consumer": "battery_h_fact_graph",
                    "implied_aux": implied_aux,
                    "aux_error": aux_error,
                }
                result = dict(attempt["result"])
                result["module_state"] = module_state
                result["message"] = (
                    "proof_battery produced a verified graph proof from old "
                    "battery h-instances."
                )
                return result, attempt["cleaned_body"], attempt["lean_code"]

    accepted, old_attempts = _first_verified_body(
        problem=problem,
        bodies=solver_core.battery_bodies(h_eq, g_eq, implied_aux=implied_aux),
        source="tool_proof_battery",
        lean_timeout_seconds=verify_timeout,
        artifact_dir=args.artifact_dir,
        max_feedback_lines=args.max_feedback_lines,
        max_feedback_chars=args.max_feedback_chars,
        max_candidates=max_candidates,
        clean=True,
    )
    attempts.extend(old_attempts)
    base_state = _module_state_from_attempts(
        module="proof_battery",
        budget=budget,
        attempts=attempts,
    )
    module_state = {
        **base_state,
        "kind": "proof_battery_tool",
        "tool": "proof_battery",
        "target": "goal",
        "elapsed": round(time.time() - started, 3),
        "verify_timeout_seconds": verify_timeout,
        "max_candidates": max_candidates,
        "include_aux": include_aux,
        "include_graph": include_graph,
        "max_graph_candidates": max_graph_candidates,
        "graph_layers_considered": graph_layers_considered,
        "implied_aux": implied_aux,
        "aux_error": aux_error,
    }
    if accepted is not None:
        result = dict(accepted["result"])
        result["module_state"] = module_state
        result["message"] = "proof_battery produced a verified old-battery proof body."
        return result, accepted["cleaned_body"], accepted["lean_code"]

    need_hint = {
        "need_hint": "choose a richer proof-generation tool or provide a bridge lemma",
        "tool": "proof_battery",
        "target": "goal",
        "attempt_count": len(attempts),
        "error_counts": base_state.get("error_counts"),
        "implied_aux": implied_aux,
        "suggestions": [
            "If battery bodies timed out or only used shallow h-instances, try forward_saturation with goal-frontier seed_terms.",
            "If an implied auxiliary lemma is listed, try lemma_hint or goal_superposition with include_aux=true for that helper.",
            "If the body excerpts show the right subterms but no equality path, propose a small bridge lemma touching the goal frontier.",
            "If no useful h-instances appeared, try certificates for collapse/grounding shapes or goal_superposition.",
        ],
        "next_tool_call_shapes": [
            {
                "kind": "tool_call",
                "tool": "forward_saturation",
                "target": "goal",
                "seed_terms": solver_core.goal_term_pool(g_eq, max_terms=6),
                "budget": min(8.0, max(5.0, budget / 2.0)),
                "why": "Old proof_battery did not close; grow h-instances from the goal frontier.",
            },
            {
                "kind": "tool_call",
                "tool": "goal_superposition",
                "target": "goal",
                "budget": min(12.0, max(8.0, budget / 2.0)),
                "include_aux": bool(implied_aux),
                "why": "Old proof_battery did not close; try proof-carrying superposition.",
            },
        ],
        "llm_tool_call_templates": [
            {
                "kind": "tool_call",
                "tool": "lemma_hint",
                "target": "goal",
                "lemmas": [
                    "<small bridge equation involving a goal subterm>",
                    "<standard helper equation if implied_aux lists one>",
                ],
                "why": (
                    "proof_battery produced concrete failed bodies; propose a "
                    "smaller untrusted lemma for the mechanical lemma consumer"
                ),
                "requires_llm_content": True,
            }
        ],
    }
    module_state["need_hint"] = need_hint
    result = {
        "status": "incorrect",
        "error_code": "TOOL_PROOF_BATTERY_STUCK",
        "message": (
            "proof_battery did not produce an accepted proof. The module state "
            "lists old-battery body attempts and verifier feedback."
        ),
        "verdict": "true",
        "module_state": module_state,
    }
    last = attempts[-1] if attempts else {}
    return result, last.get("cleaned_body", ""), last.get("lean_code", "")


def run_goal_superposition_tool(
    *,
    args: argparse.Namespace,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    tool_call: dict[str, Any],
) -> tuple[dict[str, Any], str, str]:
    started = time.time()
    raw = _as_dict(tool_call.get("raw"))
    budget = max(0.5, min(float(tool_call.get("budget") or 8.0), 30.0))
    max_candidates = max(1, min(int(raw.get("max_candidates") or raw.get("candidates") or 3), 8))
    include_aux = _tool_bool(raw, "include_aux", False)
    include_goal = _tool_bool(raw, "include_goal", True)
    implied_aux = []
    if include_aux:
        try:
            implied_aux = solver_core.implied_aux_lemmas(h_eq) if h_eq.get("free") else []
        except Exception:  # noqa: BLE001
            implied_aux = []
    verify_timeout = max(15, min(int(args.lean_timeout_seconds), int(math.ceil(max(budget, 15.0)))))
    bodies = solver_core.superposition_bodies(
        h_eq,
        g_eq,
        implied_aux=implied_aux,
        include_aux=include_aux,
        include_goal=include_goal,
        budget=budget,
    )
    accepted, attempts = _first_verified_body(
        problem=problem,
        bodies=bodies,
        source="tool_goal_superposition",
        lean_timeout_seconds=verify_timeout,
        artifact_dir=args.artifact_dir,
        max_feedback_lines=args.max_feedback_lines,
        max_feedback_chars=args.max_feedback_chars,
        max_candidates=max_candidates,
        clean=False,
    )
    base_state = _module_state_from_attempts(
        module="goal_superposition",
        budget=budget,
        attempts=attempts,
    )
    module_state = {
        **base_state,
        "kind": "superposition_tool",
        "tool": "goal_superposition",
        "target": "goal",
        "elapsed": round(time.time() - started, 3),
        "verify_timeout_seconds": verify_timeout,
        "max_candidates": max_candidates,
        "include_aux": include_aux,
        "include_goal": include_goal,
        "implied_aux": implied_aux,
    }
    if accepted is not None:
        result = dict(accepted["result"])
        result["module_state"] = module_state
        result["message"] = "goal_superposition produced a verified proof body."
        return result, accepted["cleaned_body"], accepted["lean_code"]

    need_hint = {
        "need_hint": "choose a different tool or provide a lemma/midpoint strategy",
        "tool": "goal_superposition",
        "target": "goal",
        "attempt_count": len(attempts),
        "error_counts": base_state.get("error_counts"),
        "suggestions": [
            "If superposition produced no bodies, try forward_saturation with seed_terms near the goal frontier.",
            "If bodies were rejected, inspect body_excerpt/feedback and propose a smaller lemma or lemma_chain.",
            "For square-witness hypotheses, try a lemma_chain tool or lemma_hint naming square_const/right_id_square/sandwich.",
        ],
        "llm_tool_call_templates": [
            {
                "kind": "tool_call",
                "tool": "lemma_hint",
                "target": "goal",
                "lemmas": [
                    "<small bridge equation involving the goal frontier>",
                    "<local absorption/simplification equation plausibly implied by H>",
                ],
                "why": (
                    "goal_superposition produced no accepted proof body; propose "
                    "untrusted lemmas that the mechanical side will independently prove"
                ),
                "requires_llm_content": True,
            },
            {
                "kind": "tool_call",
                "tool": "lemma_chain",
                "target": "goal",
                "lemmas": [
                    "<helper equation 1>",
                    "<helper equation 2>",
                    "<helper equation 3>",
                ],
                "why": (
                    "use when one lemma is not enough; every helper equation must "
                    "still be mechanically proved/consumed"
                ),
                "requires_llm_content": True,
            },
        ],
        "next_tool_call_shapes": [
            {
                "kind": "tool_call",
                "tool": "forward_saturation",
                "target": "goal",
                "seed_terms": solver_core.goal_term_pool(g_eq, max_terms=6),
                "budget": min(5.0, budget),
            },
            {
                "kind": "tool_call",
                "tool": "goal_superposition",
                "target": "goal",
                "budget": min(12.0, budget * 1.5),
                "max_candidates": max_candidates + 1,
            },
        ],
    }
    module_state["need_hint"] = need_hint
    result = {
        "status": "incorrect",
        "error_code": "TOOL_GOAL_SUPERPOSITION_STUCK",
        "message": (
            "goal_superposition did not produce an accepted proof. The module "
            "state lists generated proof-body attempts and verifier feedback."
        ),
        "verdict": "true",
        "module_state": module_state,
    }
    last = attempts[-1] if attempts else {}
    return result, last.get("cleaned_body", ""), last.get("lean_code", "")


def run_square_sandwich_chain_tool(
    *,
    args: argparse.Namespace,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    tool_call: dict[str, Any],
) -> tuple[dict[str, Any], str, str]:
    started = time.time()
    body, chain_state = special_square_sandwich_chain_body(h_eq, g_eq)
    module_state = dict(chain_state)
    module_state["tool"] = "square_sandwich_chain"
    module_state["target"] = "goal"
    module_state["budget_seconds"] = float(tool_call.get("budget") or 0.0)
    module_state["elapsed"] = round(time.time() - started, 3)
    if body is None:
        status = chain_state.get("status") or "not_applicable"
        need_hint = {
            "need_hint": "choose a different tool or provide the missing square-witness helper chain",
            "tool": "square_sandwich_chain",
            "target": "goal",
            "status": status,
            "expected_h_shape": "x = ((y ◇ x) ◇ y) ◇ (z ◇ z)",
            "required_helpers": [
                "u ◇ u = v ◇ v",
                "u ◇ (v ◇ v) = u",
                "(v ◇ u) ◇ v = u",
                "v ◇ (u ◇ v) = u",
            ],
            "suggestions": [
                "If H has the square-sandwich shape, return a lemma_chain naming the helper equations.",
                "If H is a row-constant shape, try forward_saturation or a rowconst lemma_hint.",
                "Otherwise try goal_superposition or forward_saturation with frontier seed terms.",
            ],
        }
        module_state["need_hint"] = need_hint
        feedback = (
            "square_sandwich_chain could not produce a proof for this problem. "
            "The module state says whether the H-shape was not applicable or "
            "normalization did not close the goal."
        )
        return {
            "status": "incorrect",
            "error_code": "TOOL_SQUARE_SANDWICH_CHAIN_NOT_CLOSED",
            "message": feedback,
            "verdict": "true",
            "module_state": module_state,
        }, "", ""

    cleaned = clean_body(body, g_eq["variables"])
    verify_timeout = max(15, min(int(args.lean_timeout_seconds), int(math.ceil(max(15.0, float(tool_call.get("budget") or 15.0))))))
    result, lean_code = verify_body(
        problem=problem,
        body=cleaned,
        lean_timeout_seconds=verify_timeout,
        artifact_dir=args.artifact_dir,
    )
    module_state["elapsed"] = round(time.time() - started, 3)
    module_state["verify_timeout_seconds"] = verify_timeout
    module_state["attempt_count"] = 1
    module_state["accepted_count"] = 1 if result.get("status") == "accepted" else 0
    module_state["error_counts"] = {result.get("error_code") or result.get("status") or "unknown": 1}
    result = dict(result)
    result["module_state"] = module_state
    if result.get("status") == "accepted":
        result["message"] = "square_sandwich_chain produced a verified helper-chain proof."
    return result, cleaned, lean_code


def run_right_square_chain_tool(
    *,
    args: argparse.Namespace,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    tool_call: dict[str, Any],
) -> tuple[dict[str, Any], str, str]:
    started = time.time()
    body = special_right_square_absorb_body(h_eq, g_eq)
    h_match = _special_right_square_absorb_h_vars(h_eq) is not None
    goal_match = _special_right_square_absorb_goal_terms(g_eq) is not None
    module_state: dict[str, Any] = {
        "kind": "right_square_chain_tool",
        "tool": "right_square_chain",
        "target": "goal",
        "h_shape_match": h_match,
        "goal_shape_match": goal_match,
        "expected_h_shape": "x = (y ◇ (y ◇ z)) ◇ (x ◇ x)",
        "expected_goal_shape": "a = a ◇ ((b ◇ (a ◇ b)) ◇ a)",
        "helper_lemmas": [
            "u ◇ (v ◇ v) = v",
            "u ◇ v = v ◇ v",
        ],
        "budget_seconds": float(tool_call.get("budget") or 0.0),
        "elapsed": round(time.time() - started, 3),
    }
    if body is None:
        need_hint = {
            "need_hint": "choose a different tool or provide a smaller helper chain",
            "tool": "right_square_chain",
            "target": "goal",
            "h_shape_match": h_match,
            "goal_shape_match": goal_match,
            "suggestions": [
                "If H has this family but the goal shape differs, try lemma_hint with `u ◇ (v ◇ v) = v` and `u ◇ v = v ◇ v` as helper targets.",
                "If the goal has a nested right operand, ask for a smaller bridge that first rewrites that operand to a square.",
                "Otherwise try goal_superposition or forward_saturation with frontier seed terms.",
            ],
            "llm_tool_call_templates": [
                {
                    "kind": "tool_call",
                    "tool": "lemma_chain",
                    "target": "goal",
                    "lemmas": [
                        {"name": "square_absorb", "equation": "u ◇ (v ◇ v) = v"},
                        {"name": "right_square", "equation": "u ◇ v = v ◇ v"},
                    ],
                    "why": "right_square_chain recognized the H family but could not close this goal shape; try the helper lemmas through the generic chain consumer.",
                    "requires_llm_content": True,
                }
            ],
        }
        module_state["need_hint"] = need_hint
        return {
            "status": "incorrect",
            "error_code": "TOOL_RIGHT_SQUARE_CHAIN_NOT_CLOSED",
            "message": (
                "right_square_chain could not produce a proof for this problem. "
                "The module state says whether H and the goal matched the supported shape."
            ),
            "verdict": "true",
            "module_state": module_state,
        }, "", ""

    cleaned = clean_body(body, g_eq["variables"])
    verify_timeout = max(15, min(int(args.lean_timeout_seconds), int(math.ceil(max(15.0, float(tool_call.get("budget") or 15.0))))))
    result, lean_code = verify_body(
        problem=problem,
        body=cleaned,
        lean_timeout_seconds=verify_timeout,
        artifact_dir=args.artifact_dir,
    )
    module_state["elapsed"] = round(time.time() - started, 3)
    module_state["verify_timeout_seconds"] = verify_timeout
    module_state["attempt_count"] = 1
    module_state["accepted_count"] = 1 if result.get("status") == "accepted" else 0
    module_state["error_counts"] = {result.get("error_code") or result.get("status") or "unknown": 1}
    result = dict(result)
    result["module_state"] = module_state
    if result.get("status") == "accepted":
        result["message"] = "right_square_chain produced a verified helper-chain proof."
    return result, cleaned, lean_code


def run_rowconst_certificates_tool(
    *,
    args: argparse.Namespace,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    tool_call: dict[str, Any],
) -> tuple[dict[str, Any], str, str]:
    started = time.time()
    raw = _as_dict(tool_call.get("raw"))
    max_candidates = max(1, min(int(raw.get("max_candidates") or raw.get("candidates") or 2), 4))
    budget = max(1.0, min(float(tool_call.get("budget") or 15.0), 30.0))
    verify_timeout = max(15, min(int(args.lean_timeout_seconds), int(math.ceil(max(15.0, budget)))))
    candidate_bodies = [
        ("tool_explicit_rowconst", special_rowconst_body(h_eq, g_eq)),
        ("tool_explicit_square_rowconst", special_square_rowconst_body(h_eq, g_eq)),
    ]
    attempts: list[dict[str, Any]] = []
    applicable = [source for source, body in candidate_bodies if body is not None]
    for source, body in candidate_bodies:
        if body is None or len(attempts) >= max_candidates:
            continue
        attempt = _verified_body_attempt(
            problem=problem,
            body=body,
            source=source,
            lean_timeout_seconds=verify_timeout,
            artifact_dir=args.artifact_dir,
            max_feedback_lines=args.max_feedback_lines,
            max_feedback_chars=args.max_feedback_chars,
        )
        attempts.append(attempt)
        if attempt.get("status") == "accepted":
            base_state = _module_state_from_attempts(
                module="rowconst_certificates",
                budget=budget,
                attempts=attempts,
            )
            module_state = {
                **base_state,
                "kind": "rowconst_certificates_tool",
                "tool": "rowconst_certificates",
                "target": "goal",
                "elapsed": round(time.time() - started, 3),
                "verify_timeout_seconds": verify_timeout,
                "max_candidates": max_candidates,
                "applicable_renderers": applicable,
            }
            result = dict(attempt["result"])
            result["module_state"] = module_state
            result["message"] = "rowconst_certificates produced a verified focused certificate proof."
            return result, attempt["cleaned_body"], attempt["lean_code"]

    base_state = _module_state_from_attempts(
        module="rowconst_certificates",
        budget=budget,
        attempts=attempts,
    )
    module_state = {
        **base_state,
        "kind": "rowconst_certificates_tool",
        "tool": "rowconst_certificates",
        "target": "goal",
        "elapsed": round(time.time() - started, 3),
        "verify_timeout_seconds": verify_timeout,
        "max_candidates": max_candidates,
        "applicable_renderers": applicable,
    }
    need_hint = {
        "need_hint": "choose another certificate tool or provide a row-constant helper lemma",
        "tool": "rowconst_certificates",
        "target": "goal",
        "applicable_renderers": applicable,
        "attempt_count": len(attempts),
        "error_counts": base_state.get("error_counts"),
        "suggestions": [
            "If no rowconst renderer applied, try certificates, square_sandwich_chain, or forward_saturation.",
            "If a rowconst renderer was rejected, inspect the body excerpt and ask for a lemma_hint matching the missing row-constant helper.",
            "If the focused renderer timed out, retry certificates with a larger budget or route to goal_superposition.",
        ],
        "next_tool_call_shapes": [
            {
                "kind": "tool_call",
                "tool": "certificates",
                "target": "goal",
                "budget": min(20.0, max(15.0, budget)),
                "max_candidates": 4,
                "why": "Focused rowconst certificates did not close; try the broader old certificate pipeline.",
            },
            {
                "kind": "tool_call",
                "tool": "forward_saturation",
                "target": "goal",
                "seed_terms": solver_core.goal_term_pool(g_eq, max_terms=6),
                "budget": min(8.0, max(5.0, budget / 2.0)),
                "why": "Focused rowconst certificates did not close; try generated h-instances around the goal.",
            },
        ],
    }
    module_state["need_hint"] = need_hint
    result = {
        "status": "incorrect",
        "error_code": "TOOL_ROWCONST_CERTIFICATES_STUCK",
        "message": (
            "rowconst_certificates did not produce an accepted proof. The module "
            "state records which focused row-constant renderers applied."
        ),
        "verdict": "true",
        "module_state": module_state,
    }
    last = attempts[-1] if attempts else {}
    return result, last.get("cleaned_body", ""), last.get("lean_code", "")


def run_certificates_tool(
    *,
    args: argparse.Namespace,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    tool_call: dict[str, Any],
) -> tuple[dict[str, Any], str, str]:
    started = time.time()
    raw = _as_dict(tool_call.get("raw"))
    max_candidates = max(1, min(int(raw.get("max_candidates") or raw.get("candidates") or 3), 8))
    budget = max(0.0, min(float(tool_call.get("budget") or 15.0), 45.0))
    verify_timeout = max(15, min(int(args.lean_timeout_seconds), int(math.ceil(max(15.0, budget)))))
    attempts: list[dict[str, Any]] = []
    explicit_bodies = [
        ("tool_explicit_rowconst", special_rowconst_body(h_eq, g_eq)),
        ("tool_explicit_square_rowconst", special_square_rowconst_body(h_eq, g_eq)),
    ]
    for source, body in explicit_bodies:
        if body is None or len(attempts) >= max_candidates:
            continue
        attempt = _verified_body_attempt(
            problem=problem,
            body=body,
            source=source,
            lean_timeout_seconds=verify_timeout,
            artifact_dir=args.artifact_dir,
            max_feedback_lines=args.max_feedback_lines,
            max_feedback_chars=args.max_feedback_chars,
        )
        attempts.append(attempt)
        if attempt.get("status") == "accepted":
            base_state = _module_state_from_attempts(
                module="certificates",
                budget=budget,
                attempts=attempts,
            )
            module_state = {
                **base_state,
                "kind": "certificates_tool",
                "tool": "certificates",
                "target": "goal",
                "elapsed": round(time.time() - started, 3),
                "verify_timeout_seconds": verify_timeout,
                "max_candidates": max_candidates,
                "explicit_consumers": [source for source, body in explicit_bodies if body is not None],
            }
            result = dict(attempt["result"])
            result["module_state"] = module_state
            result["message"] = "certificates produced a verified explicit certificate proof."
            return result, attempt["cleaned_body"], attempt["lean_code"]

    accepted, generic_attempts = _first_verified_body(
        problem=problem,
        bodies=solver_core.cert_candidates(h_eq, g_eq),
        source="tool_certificates",
        lean_timeout_seconds=verify_timeout,
        artifact_dir=args.artifact_dir,
        max_feedback_lines=args.max_feedback_lines,
        max_feedback_chars=args.max_feedback_chars,
        max_candidates=max_candidates,
        clean=False,
    )
    attempts.extend(generic_attempts)
    base_state = _module_state_from_attempts(
        module="certificates",
        budget=budget,
        attempts=attempts,
    )
    module_state = {
        **base_state,
        "kind": "certificates_tool",
        "tool": "certificates",
        "target": "goal",
        "elapsed": round(time.time() - started, 3),
        "verify_timeout_seconds": verify_timeout,
        "max_candidates": max_candidates,
    }
    if accepted is not None:
        result = dict(accepted["result"])
        result["module_state"] = module_state
        result["message"] = "certificates produced a verified proof body."
        return result, accepted["cleaned_body"], accepted["lean_code"]

    need_hint = {
        "need_hint": "choose a more specific tool or provide a lemma strategy",
        "tool": "certificates",
        "target": "goal",
        "attempt_count": len(attempts),
        "error_counts": base_state.get("error_counts"),
        "suggestions": [
            "If certificate bodies timed out, try square_sandwich_chain for square-witness H or forward_saturation with frontier seeds.",
            "If certificate bodies were rejected, use the body_excerpt and feedback to ask for a narrower lemma_hint.",
            "If no certificate bodies were produced, try goal_superposition or a standard helper lemma_hint.",
        ],
    }
    module_state["need_hint"] = need_hint
    result = {
        "status": "incorrect",
        "error_code": "TOOL_CERTIFICATES_STUCK",
        "message": (
            "certificates did not produce an accepted proof. The module state "
            "lists generated certificate attempts and verifier feedback."
        ),
        "verdict": "true",
        "module_state": module_state,
    }
    last = attempts[-1] if attempts else {}
    return result, last.get("cleaned_body", ""), last.get("lean_code", "")


def run_grounding_derived_tool(
    *,
    args: argparse.Namespace,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    tool_call: dict[str, Any],
) -> tuple[dict[str, Any], str, str]:
    started = time.time()
    raw = _as_dict(tool_call.get("raw"))
    budget = max(1.0, min(float(tool_call.get("budget") or 12.0), 25.0))
    verify_timeout = max(15, min(int(args.lean_timeout_seconds), int(math.ceil(max(15.0, budget)))))
    e1 = f"{solver_core.term_to_str(h_eq['lhs'])} = {solver_core.term_to_str(h_eq['rhs'])}"
    e2 = f"{solver_core.term_to_str(g_eq['lhs'])} = {solver_core.term_to_str(g_eq['rhs'])}"
    render_error = None
    explicit_bodies = [
        (
            "tool_grounding_derived_square_rowconst",
            special_square_rowconst_body(h_eq, g_eq),
        ),
    ]
    attempts: list[dict[str, Any]] = []
    for source, explicit_body in explicit_bodies:
        if explicit_body is None:
            continue
        attempt = _verified_body_attempt(
            problem=problem,
            body=explicit_body,
            source=source,
            lean_timeout_seconds=verify_timeout,
            artifact_dir=args.artifact_dir,
            max_feedback_lines=args.max_feedback_lines,
            max_feedback_chars=args.max_feedback_chars,
            clean=True,
        )
        attempts.append(attempt)
        if attempt.get("status") == "accepted":
            base_state = _module_state_from_attempts(
                module="grounding_derived",
                budget=budget,
                attempts=attempts,
            )
            module_state = {
                **base_state,
                "kind": "grounding_derived_tool",
                "tool": "grounding_derived",
                "target": "goal",
                "elapsed": round(time.time() - started, 3),
                "verify_timeout_seconds": verify_timeout,
                "render_error": render_error,
                "renderer": "explicit_square_rowconst",
                "renderer_budget_seconds": budget,
                "explicit_consumers": [
                    src for src, body0 in explicit_bodies if body0 is not None
                ],
                "derived_helper": "target : ∀ a b : G, a ◇ b = a ◇ a",
            }
            result = dict(attempt["result"])
            result["module_state"] = module_state
            result["message"] = (
                "grounding_derived produced a verified explicit "
                "square-rowconst proof."
            )
            return result, attempt["cleaned_body"], attempt["lean_code"]
    try:
        body = solver_core._gd_render(e1, e2, budget=budget)
    except Exception as exc:  # noqa: BLE001
        body = None
        render_error = f"{type(exc).__name__}: {exc}"

    if body is not None:
        attempts.append(_verified_body_attempt(
            problem=problem,
            body=body,
            source="tool_grounding_derived",
            lean_timeout_seconds=verify_timeout,
            artifact_dir=args.artifact_dir,
            max_feedback_lines=args.max_feedback_lines,
            max_feedback_chars=args.max_feedback_chars,
            clean=False,
        ))

    base_state = _module_state_from_attempts(
        module="grounding_derived",
        budget=budget,
        attempts=attempts,
    )
    module_state = {
        **base_state,
        "kind": "grounding_derived_tool",
        "tool": "grounding_derived",
        "target": "goal",
        "elapsed": round(time.time() - started, 3),
        "verify_timeout_seconds": verify_timeout,
        "render_error": render_error,
        "renderer": "_gd_render",
        "renderer_budget_seconds": budget,
        "explicit_consumers": [src for src, body0 in explicit_bodies if body0 is not None],
        "derived_helper_excerpt": _first_line_matching(
            body or "",
            ("have target", "have E"),
        ),
    }
    accepted = next(
        (attempt for attempt in attempts if attempt.get("status") == "accepted"),
        None,
    )
    if accepted is not None:
        result = dict(accepted["result"])
        result["module_state"] = module_state
        result["message"] = "grounding_derived produced a verified old grounding-derived certificate proof."
        return result, accepted["cleaned_body"], accepted["lean_code"]

    need_hint = {
        "need_hint": "choose another certificate/proof tool or provide the missing derived helper lemma",
        "tool": "grounding_derived",
        "target": "goal",
        "renderer": "_gd_render",
        "render_error": render_error,
        "body_produced": body is not None,
        "error_counts": base_state.get("error_counts"),
        "suggestions": [
            "If no body was produced, this H/G shape may not need a grounding-derived helper; try certificates or goal_superposition.",
            "If the generated body timed out, retry with a larger budget or use certificates as the broader old-pipeline tool.",
            "If the body was rejected, use the body excerpt to ask for a smaller lemma_hint matching the missing helper.",
        ],
        "next_tool_call_shapes": [
            {
                "kind": "tool_call",
                "tool": "certificates",
                "target": "goal",
                "budget": min(20.0, max(12.0, budget)),
                "max_candidates": 4,
                "why": "grounding_derived did not close; try the broader old certificate pipeline.",
            },
            {
                "kind": "tool_call",
                "tool": "goal_superposition",
                "target": "goal",
                "budget": min(12.0, max(8.0, budget)),
                "include_aux": True,
                "why": "grounding_derived did not close; search for proof-carrying helper lemmas directly.",
            },
        ],
    }
    module_state["need_hint"] = need_hint
    result = {
        "status": "incorrect",
        "error_code": "TOOL_GROUNDING_DERIVED_STUCK",
        "message": (
            "grounding_derived did not produce an accepted proof. The module "
            "state records whether the old renderer produced a body and how it failed."
        ),
        "verdict": "true",
        "module_state": module_state,
    }
    last = attempts[-1] if attempts else {}
    return result, last.get("cleaned_body", ""), last.get("lean_code", "")


def _table_expr_formula(table: list[list[int]]) -> str:
    n = len(table)

    def row_expr(i: int) -> str:
        expr = str(table[i][-1])
        for j in range(n - 2, -1, -1):
            expr = f"if j.val = {j} then {table[i][j]} else ({expr})"
        return expr

    expr = row_expr(n - 1)
    for i in range(n - 2, -1, -1):
        expr = f"if i.val = {i} then ({row_expr(i)}) else ({expr})"
    return f"Nat.mod ({expr}) {n}"


def lean_false_table_fn(table: list[list[int]]) -> str:
    """Axiom-clean table certificate using a function expression, not finOpTable."""
    n = len(table)
    op_formula = _table_expr_formula(table)
    return (
        "import JudgeProblem\n"
        "import JudgeDecide.DecideBang\n"
        "set_option maxRecDepth 40000\n"
        "set_option maxHeartbeats 1000000000\n"
        "def submission : Goal := by\n"
        f"  let m : Magma (Fin {n}) := {{ op := fun i j =>\n"
        f"    ⟨{op_formula}, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩ }}\n"
        f"  refine ⟨Fin {n}, m, ?_⟩\n"
        "  decideFin!\n"
    )


def _table_shape_error(table: Any) -> str | None:
    if not isinstance(table, list) or not table:
        return "table must be a non-empty square list"
    if not all(isinstance(row, list) for row in table):
        return "every table row must be a list"
    n = len(table)
    if any(len(row) != n for row in table):
        return "table must be square"
    for row in table:
        for value in row:
            if not isinstance(value, int) or value < 0 or value >= n:
                return f"table values must be integers in 0..{n - 1}"
    return None


def verify_false_table(
    *,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    table: list[list[int]],
    lean_timeout_seconds: int,
    artifact_dir: Path,
) -> tuple[dict[str, Any], str]:
    shape_error = _table_shape_error(table)
    if shape_error:
        return {
            "status": "incorrect",
            "error_code": "BAD_COUNTERMODEL_TABLE",
            "message": shape_error,
            "verdict": "false",
        }, ""
    if not solver_core.is_counterexample(h_eq, g_eq, table):
        h_holds = solver_core._eq_holds(h_eq, table)
        g_holds = solver_core._eq_holds(g_eq, table)
        return {
            "status": "incorrect",
            "error_code": "LOCAL_COUNTERMODEL_CHECK_FAILED",
            "message": (
                "The proposed table is not a countermodel: "
                f"H_holds={h_holds}, G_holds={g_holds}."
            ),
            "verdict": "false",
            "local_check": {"H_holds": h_holds, "G_holds": g_holds},
        }, ""

    code = lean_false_table_fn(table)
    answer = json.dumps({"verdict": "false", "code": code})
    cfg = JudgeConfig(
        artifact_dir=artifact_dir,
        lean_timeout_seconds=lean_timeout_seconds,
        max_code_length=100_000,
        max_false_cert_bytes=20_000,
    )
    try:
        result = verify_answer(problem, answer, config=cfg)
    except Exception as exc:  # noqa: BLE001
        result = {
            "status": "verifier_error",
            "error_code": "VERIFY_EXCEPTION",
            "message": f"Verifier raised {type(exc).__name__}: {exc}",
            "verdict": "false",
        }
    result = dict(result)
    result["local_check"] = {"H_holds": True, "G_holds": False}
    return result, code


def _verified_body_attempt(
    *,
    problem: dict[str, Any],
    body: str,
    source: str,
    lean_timeout_seconds: int,
    artifact_dir: Path,
    max_feedback_lines: int,
    max_feedback_chars: int,
    clean: bool = True,
) -> dict[str, Any]:
    cleaned = clean_body(body, parse_problem(problem)[1]["variables"]) if clean else body.strip()
    result, lean_code = verify_body(
        problem=problem,
        body=cleaned,
        lean_timeout_seconds=lean_timeout_seconds,
        artifact_dir=artifact_dir,
    )
    return {
        "source": source,
        "raw_body": body,
        "cleaned_body": cleaned,
        "lean_code": lean_code,
        "status": result.get("status"),
        "error_code": result.get("error_code"),
        "feedback": feedback_from_result(
            result,
            max_lines=max_feedback_lines,
            max_chars=max_feedback_chars,
        ),
        "result": result,
    }


def _first_verified_body(
    *,
    problem: dict[str, Any],
    bodies: Any,
    source: str,
    lean_timeout_seconds: int,
    artifact_dir: Path,
    max_feedback_lines: int,
    max_feedback_chars: int,
    max_candidates: int = 3,
    clean: bool = True,
) -> tuple[dict[str, Any] | None, list[dict[str, Any]]]:
    attempts: list[dict[str, Any]] = []
    for body in bodies:
        if len(attempts) >= max_candidates:
            break
        attempt = _verified_body_attempt(
            problem=problem,
            body=body,
            source=source,
            lean_timeout_seconds=lean_timeout_seconds,
            artifact_dir=artifact_dir,
            max_feedback_lines=max_feedback_lines,
            max_feedback_chars=max_feedback_chars,
            clean=clean,
        )
        attempts.append(attempt)
        if attempt["status"] == "accepted":
            return attempt, attempts
    return None, attempts


def _module_state_from_attempts(
    *,
    module: str,
    budget: float,
    attempts: list[dict[str, Any]],
) -> dict[str, Any]:
    accepted = [attempt for attempt in attempts if attempt.get("status") == "accepted"]
    error_counts: dict[str, int] = {}
    for attempt in attempts:
        key = attempt.get("error_code") or attempt.get("status") or "unknown"
        error_counts[key] = error_counts.get(key, 0) + 1
    return {
        "kind": "mechanical_module_state",
        "module": module,
        "status": "accepted" if accepted else "no_accepted_body",
        "budget_seconds": budget,
        "attempt_count": len(attempts),
        "accepted_count": len(accepted),
        "error_counts": error_counts,
        "failure_summary": (
            "accepted proof body produced"
            if accepted
            else (
                "no candidate bodies were produced"
                if not attempts
                else "candidate bodies were produced but none were accepted"
            )
        ),
        "attempts": [
            {
                "source": attempt.get("source"),
                "status": attempt.get("status"),
                "error_code": attempt.get("error_code"),
                "feedback": (attempt.get("feedback") or "")[:1200],
                "body_excerpt": (attempt.get("cleaned_body") or "")[:1600],
            }
            for attempt in attempts[-3:]
        ],
    }


def verify_lemma_hint(
    *,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    lemma_hint: dict[str, Any],
    max_h_facts: int,
    max_lemma_facts: int,
    congruence_depth: int,
    max_congruence_facts: int,
    lemma_superposition_budget: float,
    midpoint_superposition_budget: float,
    standard_lemma_cert_budget: float,
    lemma_ce_time_budget: float,
    lean_timeout_seconds: int,
    artifact_dir: Path,
    max_feedback_lines: int,
    max_feedback_chars: int,
) -> tuple[dict[str, Any], str, str]:
    lemma_eq = lemma_hint["eq"]
    seed_h_args = lemma_hint.get("seed_h_args") or []
    use_args = lemma_hint.get("use_args") or []
    standard_kind = standard_lemma_kind(lemma_eq)
    square_sandwich_kind = _square_sandwich_lemma_kind(lemma_eq)
    lifecycle: dict[str, Any] = {
        "kind": "lemma_lifecycle",
        "equation": lemma_hint["equation_text"],
        "parsed": True,
        "standard_kind": standard_kind,
        "square_sandwich_kind": square_sandwich_kind,
        "small_model_plausible": None,
        "proved": False,
        "proof_source": None,
        "used_for_goal": False,
        "use_source": None,
    }
    standard_cert_state: dict[str, Any] | None = None
    try:
        implied_aux = solver_core.implied_aux_lemmas(h_eq) if h_eq.get("free") else []
    except Exception:  # noqa: BLE001
        implied_aux = []

    if lemma_ce_time_budget > 0:
        try:
            counterexample = solver_core.find_counterexample(
                h_eq,
                lemma_eq,
                max_n=3,
                time_budget=lemma_ce_time_budget,
            )
        except Exception:  # noqa: BLE001
            counterexample = None
        if counterexample is not None:
            lifecycle["small_model_plausible"] = False
            feedback = (
                f"Lemma `{lemma_hint['equation_text']}` is refuted by a small "
                "model satisfying H, so it cannot be used. Propose a weaker or "
                "different lemma."
            )
            return {
                "status": "incorrect",
                "error_code": "LEMMA_REFUTED_SMALL_MODEL",
                "message": feedback,
                "verdict": "true",
                "counterexample_size": len(counterexample),
                "lemma_lifecycle": lifecycle,
            }, "", ""
        lifecycle["small_model_plausible"] = True

    if (
        standard_lemma_cert_budget > 0
        and standard_kind is not None
        and standard_kind in implied_aux
    ):
        explicit_body = None
        if standard_kind == "rowconst":
            explicit_body = (
                special_rowconst_body(h_eq, g_eq)
                or special_square_rowconst_body(h_eq, g_eq)
            )
        if explicit_body is not None:
            explicit_attempt = _verified_body_attempt(
                problem=problem,
                body=explicit_body,
                source=f"explicit_{standard_kind}_hint",
                lean_timeout_seconds=lean_timeout_seconds,
                artifact_dir=artifact_dir,
                max_feedback_lines=max_feedback_lines,
                max_feedback_chars=max_feedback_chars,
            )
            standard_cert_state = _module_state_from_attempts(
                module=f"explicit_{standard_kind}_hint",
                budget=standard_lemma_cert_budget,
                attempts=[explicit_attempt],
            )
            if explicit_attempt["status"] == "accepted":
                lifecycle["proved"] = True
                lifecycle["proof_source"] = f"explicit_standard_{standard_kind}"
                lifecycle["used_for_goal"] = True
                lifecycle["use_source"] = f"explicit_standard_{standard_kind}"
                result = dict(explicit_attempt["result"])
                result["message"] = (
                    f"LLM suggested standard lemma `{standard_kind}`; "
                    "explicit standard-lemma renderer produced a verified goal proof."
                )
                result["lemma_source"] = f"explicit_standard_{standard_kind}"
                result["module_state"] = standard_cert_state
                result["lemma_lifecycle"] = lifecycle
                return result, explicit_attempt["cleaned_body"], explicit_attempt["lean_code"]

        accepted, attempts = _first_verified_body(
            problem=problem,
            bodies=solver_core.cert_candidates(h_eq, g_eq),
            source=f"cert_after_{standard_kind}_hint",
            lean_timeout_seconds=lean_timeout_seconds,
            artifact_dir=artifact_dir,
            max_feedback_lines=max_feedback_lines,
            max_feedback_chars=max_feedback_chars,
            max_candidates=3,
        )
        standard_cert_state = _module_state_from_attempts(
            module=f"cert_after_{standard_kind}_hint",
            budget=standard_lemma_cert_budget,
            attempts=attempts,
        )
        if accepted is not None:
            lifecycle["proved"] = True
            lifecycle["proof_source"] = f"standard_{standard_kind}_certificates"
            lifecycle["used_for_goal"] = True
            lifecycle["use_source"] = f"standard_{standard_kind}_certificates"
            result = dict(accepted["result"])
            result["message"] = (
                f"LLM suggested standard lemma `{standard_kind}`; "
                "certificate consumer produced a verified goal proof."
            )
            result["lemma_source"] = f"standard_{standard_kind}_certificates"
            result["module_state"] = standard_cert_state
            result["lemma_lifecycle"] = lifecycle
            return result, accepted["cleaned_body"], accepted["lean_code"]

    if standard_lemma_cert_budget > 0 and square_sandwich_kind is not None:
        explicit_body, chain_state = special_square_sandwich_chain_body(h_eq, g_eq)
        if explicit_body is not None:
            explicit_attempt = _verified_body_attempt(
                problem=problem,
                body=explicit_body,
                source=f"explicit_square_sandwich_after_{square_sandwich_kind}_hint",
                lean_timeout_seconds=lean_timeout_seconds,
                artifact_dir=artifact_dir,
                max_feedback_lines=max_feedback_lines,
                max_feedback_chars=max_feedback_chars,
            )
            module_state = _module_state_from_attempts(
                module=f"explicit_square_sandwich_after_{square_sandwich_kind}_hint",
                budget=standard_lemma_cert_budget,
                attempts=[explicit_attempt],
            )
            module_state["chain_state"] = chain_state
            if explicit_attempt["status"] == "accepted":
                lifecycle["proved"] = True
                lifecycle["proof_source"] = "explicit_square_sandwich_chain"
                lifecycle["used_for_goal"] = True
                lifecycle["use_source"] = "explicit_square_sandwich_chain"
                result = dict(explicit_attempt["result"])
                result["message"] = (
                    f"LLM suggested square-witness lemma `{square_sandwich_kind}`; "
                    "explicit chain renderer produced a verified goal proof."
                )
                result["lemma_source"] = "explicit_square_sandwich_chain"
                result["module_state"] = module_state
                result["lemma_lifecycle"] = lifecycle
                return result, explicit_attempt["cleaned_body"], explicit_attempt["lean_code"]
        elif chain_state.get("status") != "not_applicable":
            lifecycle["proof_source"] = "explicit_square_sandwich_chain_not_closed"

    lemma_body = h_graph_body(
        h_eq,
        lemma_eq,
        max_h_facts,
        extra_args=seed_h_args,
        congruence_depth=congruence_depth,
        max_congruence_facts=max_congruence_facts,
    )
    lemma_source = "h_fact_graph"
    lemma_module_state: dict[str, Any] | None = None
    if lemma_body is None:
        if lemma_superposition_budget > 0:
            lemma_problem = dict(problem)
            lemma_problem["id"] = f"{problem.get('id', 'problem')}.lemma.superposition"
            lemma_problem["equation2"] = lemma_hint["equation_text"]
            accepted, attempts = _first_verified_body(
                problem=lemma_problem,
                bodies=solver_core.superposition_bodies(
                    h_eq,
                    lemma_eq,
                    include_aux=False,
                    include_goal=True,
                    budget=lemma_superposition_budget,
                ),
                source="lemma_superposition",
                lean_timeout_seconds=lean_timeout_seconds,
                artifact_dir=artifact_dir,
                max_feedback_lines=max_feedback_lines,
                max_feedback_chars=max_feedback_chars,
                max_candidates=3,
            )
            lemma_module_state = _module_state_from_attempts(
                module="lemma_superposition",
                budget=lemma_superposition_budget,
                attempts=attempts,
            )
            if accepted is not None:
                lemma_body = accepted["cleaned_body"]
                lemma_source = "lemma_superposition"

        if lemma_body is None:
            feedback = (
                f"Lemma `{lemma_hint['equation_text']}` could not be proved by the "
                "h-fact graph"
                + (
                    " or the enabled superposition fallback"
                    if lemma_superposition_budget > 0
                    else ""
                )
                + ". Try a smaller lemma or add seed_h_args whose h-facts "
                "connect the lemma's left and right sides.\n\n"
                + h_graph_diagnostics(
                    h_eq,
                    lemma_eq,
                    max_h_facts,
                    extra_args=seed_h_args,
                )
            )
            state = build_search_state(
                h_eq,
                lemma_eq,
                max_h_facts,
                extra_args=seed_h_args,
                congruence_depth=congruence_depth,
                max_congruence_facts=max_congruence_facts,
                status="stuck",
                failed_hints=[{
                    "kind": "lemma_hint",
                    "equation": lemma_hint["equation_text"],
                    "failure": "lemma_not_proved",
                }],
            )
            if state.get("need_hint"):
                feedback += (
                    "\n\nMost useful next hint request:\n"
                    + search_state_text(state["need_hint"], max_chars=1200)
                )
            result = {
                "status": "incorrect",
                "error_code": "LEMMA_GRAPH_NO_PATH",
                "message": feedback,
                "verdict": "true",
                "search_state": state,
                "lemma_lifecycle": lifecycle,
            }
            if lemma_module_state is not None or standard_cert_state is not None:
                result["module_state"] = lemma_module_state or standard_cert_state
            return result, "", ""

    lemma_problem = dict(problem)
    lemma_problem["id"] = f"{problem.get('id', 'problem')}.lemma"
    lemma_problem["equation2"] = lemma_hint["equation_text"]
    if lemma_source == "lemma_superposition":
        lifecycle["proved"] = True
        lifecycle["proof_source"] = "lemma_superposition"
        lemma_result = {"status": "accepted", "message": "accepted by superposition"}
        lemma_code = solver_core.lean_true(lemma_body)
    else:
        lemma_result, lemma_code = verify_body(
            problem=lemma_problem,
            body=lemma_body,
            lean_timeout_seconds=lean_timeout_seconds,
            artifact_dir=artifact_dir,
        )
        if lemma_result.get("status") != "accepted":
            feedback = "Lemma proof was synthesized but rejected by Lean:\n"
            feedback += feedback_from_result(
                lemma_result,
                max_lines=max_feedback_lines,
                max_chars=max_feedback_chars,
            )
            lemma_result = dict(lemma_result)
            lemma_result["message"] = feedback
            lifecycle["proof_source"] = "h_fact_graph_rejected_by_lean"
            lemma_result["lemma_lifecycle"] = lifecycle
            return lemma_result, lemma_body, lemma_code
        lifecycle["proved"] = True
        lifecycle["proof_source"] = "h_fact_graph"

    goal_body = h_graph_body(
        h_eq,
        g_eq,
        max_h_facts,
        extra_args=seed_h_args,
        lemmas=[{
            "name": "mid",
            "eq": lemma_eq,
            "extra_args": use_args,
        }],
        lemma_fact_limit=max_lemma_facts,
        congruence_depth=congruence_depth,
        max_congruence_facts=max_congruence_facts,
    )
    if goal_body is None:
        state = build_search_state(
            h_eq,
            g_eq,
            max_h_facts,
            extra_args=seed_h_args,
            lemmas=[{
                "name": "mid",
                "eq": lemma_eq,
                "extra_args": use_args,
            }],
            lemma_fact_limit=max_lemma_facts,
            congruence_depth=congruence_depth,
            max_congruence_facts=max_congruence_facts,
            status="stuck",
            failed_hints=[{
                "kind": "lemma_hint",
                "equation": lemma_hint["equation_text"],
                "failure": "lemma_proved_but_goal_not_connected",
            }],
        )
        instance_diag = lemma_instance_diagnostics(
            h_eq,
            g_eq,
            max_h_facts,
            lemma={
                "name": "mid",
                "eq": lemma_eq,
                "extra_args": use_args,
            },
            extra_args=seed_h_args,
            lemma_fact_limit=max_lemma_facts,
            congruence_depth=congruence_depth,
            max_congruence_facts=max_congruence_facts,
        )
        state["lemma_instance_diagnostics"] = instance_diag
        if midpoint_superposition_budget > 0:
            accepted, attempts = _first_verified_body(
                problem=problem,
                bodies=solver_core.midpoint_stitched_bodies(
                    h_eq,
                    g_eq,
                    lemma_eq,
                    budget=midpoint_superposition_budget,
                ),
                source="midpoint_superposition",
                lean_timeout_seconds=lean_timeout_seconds,
                artifact_dir=artifact_dir,
                max_feedback_lines=max_feedback_lines,
                max_feedback_chars=max_feedback_chars,
                max_candidates=3,
            )
            module_state = _module_state_from_attempts(
                module="midpoint_superposition",
                budget=midpoint_superposition_budget,
                attempts=attempts,
            )
            if accepted is not None:
                lifecycle["used_for_goal"] = True
                lifecycle["use_source"] = "midpoint_superposition"
                result = dict(accepted["result"])
                result["message"] = (
                    "LLM lemma was accepted by the midpoint superposition adapter."
                )
                result["lemma_source"] = lemma_source
                result["module_state"] = module_state
                result["lemma_lifecycle"] = lifecycle
                return result, accepted["cleaned_body"], accepted["lean_code"]
            state["module_state"] = module_state
        feedback = (
            f"Lemma `{lemma_hint['equation_text']}` was proved, but the goal graph "
            "still found no path using it"
            + (
                ", and the enabled midpoint superposition adapter did not close "
                "the full proof"
                if midpoint_superposition_budget > 0
                else ""
            )
            + ". Try a lemma whose instantiated left or right side touches one "
            "component of the goal while the other side touches the other component."
        )
        if state.get("need_hint"):
            feedback += (
                "\n\nMost useful next hint request:\n"
                + search_state_text(state["need_hint"], max_chars=1200)
            )
        feedback += (
            "\n\nLemma instance diagnostics:\n"
            + search_state_text(instance_diag, max_chars=2500)
        )
        return {
            "status": "incorrect",
            "error_code": "LEMMA_PROVED_GOAL_NO_PATH",
            "message": feedback,
            "verdict": "true",
            "search_state": state,
            "lemma_source": lemma_source,
            "module_state": state.get("module_state") or standard_cert_state,
            "lemma_lifecycle": lifecycle,
        }, lemma_body, lemma_code

    lifecycle["used_for_goal"] = True
    lifecycle["use_source"] = "h_fact_graph"
    full_body = (
        f"have mid : {lemma_statement(lemma_eq)} := by\n"
        f"{indent_lean(lemma_body, 2)}\n"
        f"{goal_body}"
    )
    result, lean_code = verify_body(
        problem=problem,
        body=full_body,
        lean_timeout_seconds=lean_timeout_seconds,
        artifact_dir=artifact_dir,
    )
    if result.get("status") != "accepted":
        feedback = "Lemma was proved and used in a synthesized goal proof, but Lean rejected the combined proof:\n"
        feedback += feedback_from_result(
            result,
            max_lines=max_feedback_lines,
            max_chars=max_feedback_chars,
        )
        result = dict(result)
        result["message"] = feedback
    result = dict(result)
    result["lemma_source"] = lemma_source
    result["lemma_lifecycle"] = lifecycle
    if lemma_module_state is not None:
        result["module_state"] = lemma_module_state
    elif standard_cert_state is not None:
        result["module_state"] = standard_cert_state
    return result, full_body, lean_code


def preseed_mechanical_attempts(
    *,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    count: int,
    lean_timeout_seconds: int,
    artifact_dir: Path,
    max_feedback_lines: int,
    max_feedback_chars: int,
) -> list[dict[str, Any]]:
    """Run a few cheap mechanical bodies and return their feedback as hints.

    These are not trusted or hidden. They become part of the prompt as previous
    attempts, so the LLM sees concrete Lean code plus the verifier's reason it
    did not close.
    """
    if count <= 0:
        return []
    attempts: list[dict[str, Any]] = []
    try:
        implied_aux = solver_core.implied_aux_lemmas(h_eq) if h_eq.get("free") else None
    except Exception:
        implied_aux = None
    generators = [
        ("battery", solver_core.battery_bodies(h_eq, g_eq, implied_aux=implied_aux)),
        ("saturation", solver_core.saturation_bodies(h_eq, g_eq)),
    ]
    for source, bodies in generators:
        for body in bodies:
            if len(attempts) >= count:
                return attempts
            cleaned = clean_body(body, g_eq["variables"])
            result, lean_code = verify_body(
                problem=problem,
                body=cleaned,
                lean_timeout_seconds=lean_timeout_seconds,
                artifact_dir=artifact_dir,
            )
            feedback = feedback_from_result(
                result,
                max_lines=max_feedback_lines,
                max_chars=max_feedback_chars,
            )
            attempts.append({
                "round": f"mechanical-{len(attempts)}",
                "source": source,
                "raw_body": body,
                "llm_payload": {"kind": "mechanical_preseed", "source": source},
                "cleaned_body": cleaned,
                "lean_code": lean_code,
                "status": result.get("status"),
                "error_code": result.get("error_code"),
                "feedback": feedback,
                "result": result,
            })
            if result.get("status") == "accepted":
                return attempts
    return attempts


def lemma_hint_attempt_from_response(
    *,
    args: argparse.Namespace,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    round_idx: int | str,
    llm_response: dict[str, Any],
) -> dict[str, Any]:
    lemma_hints, llm_payload = extract_lemma_hints(
        llm_response.get("response", ""),
        h_nargs=len(h_eq["variables"]),
    )
    if not lemma_hints:
        feedback = (
            "Protocol failure: return one JSON object with an `equation` field "
            "or a `lemmas`/`lemma_hints` list. Each candidate should contain only "
            "an equation, plus optional `seed_h_args` and `use_args` lists."
        )
        if isinstance(llm_payload, dict) and llm_payload.get("parse_error"):
            feedback += f"\nParse error: {llm_payload['parse_error']}"
        return {
            "round": round_idx,
            "raw_body": llm_response.get("response", ""),
            "llm_payload": llm_payload,
            "cleaned_body": "",
            "lean_code": "",
            "status": "protocol_rejected",
            "error_code": "BAD_LEMMA_HINT",
            "feedback": feedback,
            "result": {"status": "protocol_rejected", "message": feedback},
        }

    ranked_hints = rank_lemma_hints(lemma_hints, g_eq)
    candidate_summaries: list[dict[str, Any]] = []
    last_attempt: dict[str, Any] | None = None
    for lemma_hint in ranked_hints:
        result, built_body, lean_code = verify_lemma_hint(
            problem=problem,
            h_eq=h_eq,
            g_eq=g_eq,
            lemma_hint=lemma_hint,
            max_h_facts=args.max_h_facts,
            max_lemma_facts=args.max_lemma_facts,
            congruence_depth=args.congruence_depth,
            max_congruence_facts=args.max_congruence_facts,
            lemma_superposition_budget=args.lemma_superposition_budget,
            midpoint_superposition_budget=args.midpoint_superposition_budget,
            standard_lemma_cert_budget=args.standard_lemma_cert_budget,
            lemma_ce_time_budget=args.lemma_ce_time_budget,
            lean_timeout_seconds=args.lean_timeout_seconds,
            artifact_dir=args.artifact_dir,
            max_feedback_lines=args.max_feedback_lines,
            max_feedback_chars=args.max_feedback_chars,
        )
        feedback = feedback_from_result(
            result,
            max_lines=args.max_feedback_lines,
            max_chars=args.max_feedback_chars,
        )
        attempt = {
            "round": round_idx,
            "raw_body": llm_response.get("response", ""),
            "llm_payload": llm_payload,
            "lemma_hint": {
                "equation": lemma_hint["equation_text"],
                "seed_h_args": lemma_hint.get("seed_h_args") or [],
                "use_args": lemma_hint.get("use_args") or [],
                "rank": lemma_hint.get("rank"),
                "rank_score": lemma_hint.get("rank_score"),
                "syntax_repair": lemma_hint.get("syntax_repair"),
            },
            "cleaned_body": built_body,
            "lean_code": lean_code,
            "status": result.get("status"),
            "error_code": result.get("error_code"),
            "feedback": feedback,
            "result": result,
            "search_state": result.get("search_state"),
            "module_state": result.get("module_state"),
            "lemma_lifecycle": result.get("lemma_lifecycle"),
        }
        candidate_summaries.append({
            "equation": lemma_hint["equation_text"],
            "rank": lemma_hint.get("rank"),
            "rank_score": lemma_hint.get("rank_score"),
            "syntax_repair": lemma_hint.get("syntax_repair"),
            "status": result.get("status"),
            "error_code": result.get("error_code"),
            "lemma_lifecycle": result.get("lemma_lifecycle"),
        })
        attempt["candidate_summaries"] = candidate_summaries
        last_attempt = attempt
        if result.get("status") == "accepted":
            return attempt

    assert last_attempt is not None
    last_attempt["feedback"] += (
        "\n\nAll ranked lemma candidates failed:\n"
        + search_state_text(candidate_summaries, max_chars=2500)
    )
    return last_attempt


def _safe_lean_name(raw: Any, fallback: str) -> str:
    name = str(raw or "").strip()
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", name) and name not in {"by", "have", "intro", "exact"}:
        return name
    return fallback


def _unique_lemma_name(base: str, used: set[str]) -> str:
    candidate = base
    idx = 2
    while candidate in used:
        candidate = f"{base}_{idx}"
        idx += 1
    used.add(candidate)
    return candidate


def _generic_multi_lemma_chain_body(
    *,
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    chain_hint: dict[str, Any],
    max_h_facts: int,
    max_lemma_facts: int,
    congruence_depth: int,
    max_congruence_facts: int,
) -> tuple[str | None, dict[str, Any]]:
    """Prove a proposed helper chain, then let the h-fact graph consume all helpers.

    This is intentionally bounded. Family-specific helper packs may prove several
    canonical lemmas at once, but the final goal use still goes through the
    generic multi-lemma graph consumer.
    """
    used_names: set[str] = set()
    proof_lines: list[str] = []
    available_lemmas: list[dict[str, Any]] = []
    proved: list[dict[str, Any]] = []
    failed: list[dict[str, Any]] = []
    all_seed_h_args: list[tuple[str, ...]] = []
    right_square_kinds = {
        lemma.get("kind")
        for lemma in chain_hint["lemmas"]
        if lemma.get("kind") in {"square_absorb", "right_square"}
    }

    if (
        _special_right_square_absorb_h_vars(h_eq) is not None
        and {"square_absorb", "right_square"} <= right_square_kinds
    ):
        helper_lines = _right_square_absorb_helper_lines(h_eq)
        if helper_lines is not None:
            proof_lines.extend(helper_lines)
            for kind in ("square_absorb", "right_square"):
                lemma_eq = solver_core.parse_equation(
                    solver_core.normalize(RIGHT_SQUARE_HELPER_EQUATIONS[kind])
                )
                used_names.add(kind)
                available_lemmas.append({
                    "name": kind,
                    "eq": lemma_eq,
                    "extra_args": [],
                })
                proved.append({
                    "name": kind,
                    "equation": lemma_eq["text"],
                    "proof_source": "explicit_right_square_helper_pack",
                })

    for idx, lemma in enumerate(chain_hint["lemmas"], start=1):
        kind = lemma.get("kind")
        if kind in right_square_kinds and kind in {"square_absorb", "right_square"}:
            continue
        lemma_eq = lemma["eq"]
        base_name = kind or _safe_lean_name(lemma.get("name"), f"chain_lemma_{idx}")
        name = _unique_lemma_name(base_name, used_names)
        seed_h_args = lemma.get("seed_h_args") or []
        all_seed_h_args.extend(seed_h_args)
        lemma_body = h_graph_body(
            h_eq,
            lemma_eq,
            max_h_facts,
            extra_args=seed_h_args,
            congruence_depth=congruence_depth,
            max_congruence_facts=max_congruence_facts,
        )
        if lemma_body is None:
            state = build_search_state(
                h_eq,
                lemma_eq,
                max_h_facts,
                extra_args=seed_h_args,
                congruence_depth=congruence_depth,
                max_congruence_facts=max_congruence_facts,
                status="stuck",
                failed_hints=[{
                    "kind": "lemma_chain",
                    "equation": lemma_eq["text"],
                    "failure": "chain_lemma_not_proved",
                }],
            )
            failed.append({
                "name": name,
                "equation": lemma_eq["text"],
                "error_code": "CHAIN_LEMMA_GRAPH_NO_PATH",
                "search_state": state,
            })
            return None, {
                "kind": "generic_lemma_chain",
                "status": "lemma_not_proved",
                "proved_lemmas": proved,
                "failed_lemmas": failed,
                "need_hint": state.get("need_hint"),
            }
        proof_lines.append(
            f"have {name} : {lemma_statement(lemma_eq)} := by\n"
            f"{indent_lean(lemma_body, 2)}"
        )
        available_lemmas.append({
            "name": name,
            "eq": lemma_eq,
            "extra_args": lemma.get("use_args") or [],
        })
        proved.append({
            "name": name,
            "equation": lemma_eq["text"],
            "proof_source": "h_fact_graph",
        })

    if not available_lemmas:
        return None, {
            "kind": "generic_lemma_chain",
            "status": "no_proved_lemmas",
            "reason": "No proposed chain lemma could be proved or supplied by a helper pack.",
        }

    chain_congruence_depth = max(congruence_depth, 1 if len(available_lemmas) >= 2 else congruence_depth)
    chain_congruence_cap = max(max_congruence_facts, 1600 if right_square_kinds else max_congruence_facts)
    chain_lemma_fact_limit = max(max_lemma_facts, 160 if right_square_kinds else max_lemma_facts)
    goal_body = h_graph_body(
        h_eq,
        g_eq,
        max_h_facts,
        extra_args=all_seed_h_args,
        lemmas=available_lemmas,
        lemma_fact_limit=chain_lemma_fact_limit,
        congruence_depth=chain_congruence_depth,
        max_congruence_facts=chain_congruence_cap,
    )
    if goal_body is None:
        state = build_search_state(
            h_eq,
            g_eq,
            max_h_facts,
            extra_args=all_seed_h_args,
            lemmas=available_lemmas,
            lemma_fact_limit=chain_lemma_fact_limit,
            congruence_depth=chain_congruence_depth,
            max_congruence_facts=chain_congruence_cap,
            status="stuck",
            failed_hints=[{
                "kind": "lemma_chain",
                "failure": "proved_chain_not_consumed",
            }],
        )
        diagnostics = [
            lemma_instance_diagnostics(
                h_eq,
                g_eq,
                max_h_facts,
                lemma=lemma,
                extra_args=all_seed_h_args,
                lemma_fact_limit=chain_lemma_fact_limit,
                congruence_depth=chain_congruence_depth,
                max_congruence_facts=chain_congruence_cap,
            )
            for lemma in available_lemmas[:5]
        ]
        state["lemma_instance_diagnostics"] = diagnostics
        return None, {
            "kind": "generic_lemma_chain",
            "status": "goal_not_connected",
            "proved_lemmas": proved,
            "search_state": state,
            "need_hint": state.get("need_hint"),
        }

    goal_lines = goal_body.splitlines()
    if goal_lines and re.match(r"^\s*intro\b", goal_lines[0]):
        full_lines = [goal_lines[0], *proof_lines, *goal_lines[1:]]
    else:
        full_lines = [*proof_lines, goal_body]
    return "\n".join(full_lines), {
        "kind": "generic_lemma_chain",
        "status": "body_built",
        "proved_lemmas": proved,
        "consumer": "h_fact_graph_multi_lemma",
        "goal_congruence_depth": chain_congruence_depth,
        "goal_max_congruence_facts": chain_congruence_cap,
        "goal_max_lemma_facts": chain_lemma_fact_limit,
    }


def lemma_chain_attempt_from_response(
    *,
    args: argparse.Namespace,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    round_idx: int | str,
    llm_response: dict[str, Any],
) -> dict[str, Any]:
    chain_hint, llm_payload = extract_lemma_chain_hint(
        llm_response.get("response", ""),
        h_nargs=len(h_eq["variables"]),
    )
    if chain_hint is None:
        feedback = (
            "Protocol failure: return one JSON object with a `lemmas` list. "
            "Each lemma should be an equation string or an object with `name` "
            "and `equation`."
        )
        return {
            "round": round_idx,
            "raw_body": llm_response.get("response", ""),
            "llm_payload": llm_payload,
            "cleaned_body": "",
            "lean_code": "",
            "status": "protocol_rejected",
            "error_code": "BAD_LEMMA_CHAIN",
            "feedback": feedback,
            "result": {"status": "protocol_rejected", "message": feedback},
        }

    chain_summary = {
        "kind": "lemma_chain",
        "witness_term": chain_hint.get("witness_term"),
        "lemmas": [
            {
                "name": lemma.get("name"),
                "equation": lemma.get("equation_text"),
                "original_equation": lemma.get("original_equation_text"),
                "kind": lemma.get("kind"),
                "seed_h_args": lemma.get("seed_h_args") or [],
                "use_args": lemma.get("use_args") or [],
                "syntax_repair": lemma.get("syntax_repair"),
            }
            for lemma in chain_hint["lemmas"]
        ],
    }
    generic_body, generic_state = _generic_multi_lemma_chain_body(
        h_eq=h_eq,
        g_eq=g_eq,
        chain_hint=chain_hint,
        max_h_facts=args.max_h_facts,
        max_lemma_facts=args.max_lemma_facts,
        congruence_depth=args.congruence_depth,
        max_congruence_facts=args.max_congruence_facts,
    )
    if generic_body is not None:
        cleaned = clean_body(generic_body, g_eq["variables"])
        result, lean_code = verify_body(
            problem=problem,
            body=cleaned,
            lean_timeout_seconds=args.lean_timeout_seconds,
            artifact_dir=args.artifact_dir,
        )
        feedback = feedback_from_result(
            result,
            max_lines=args.max_feedback_lines,
            max_chars=args.max_feedback_chars,
        )
        result = dict(result)
        result["chain_state"] = generic_state
        if result.get("status") == "accepted":
            result["message"] = "generic lemma_chain proved and consumed multiple helper equations."
        return {
            "round": round_idx,
            "raw_body": llm_response.get("response", ""),
            "llm_payload": llm_payload,
            "lemma_chain": chain_summary,
            "cleaned_body": cleaned,
            "lean_code": lean_code,
            "status": result.get("status"),
            "error_code": result.get("error_code"),
            "feedback": feedback,
            "result": result,
            "module_state": generic_state,
        }

    right_square_kinds = {
        lemma.get("kind")
        for lemma in chain_hint["lemmas"]
        if lemma.get("kind") in {"square_absorb", "right_square"}
    }
    square_sandwich_h = _special_square_sandwich_h_vars(h_eq) is not None
    if right_square_kinds or not square_sandwich_h:
        feedback = (
            "The lemma chain parsed, but the generic multi-lemma consumer could "
            "not prove and use the helpers.\n\n"
            + search_state_text(generic_state, max_chars=3000)
        )
        return {
            "round": round_idx,
            "raw_body": llm_response.get("response", ""),
            "llm_payload": llm_payload,
            "lemma_chain": chain_summary,
            "cleaned_body": "",
            "lean_code": "",
            "status": "incorrect",
            "error_code": "GENERIC_LEMMA_CHAIN_NOT_CONSUMED",
            "feedback": feedback,
            "result": {
                "status": "incorrect",
                "error_code": "GENERIC_LEMMA_CHAIN_NOT_CONSUMED",
                "message": feedback,
                "chain_state": generic_state,
            },
            "module_state": generic_state,
            "search_state": generic_state.get("search_state"),
        }

    required = {"square_const", "right_id_square", "sandwich"}
    kinds = {lemma.get("kind") for lemma in chain_hint["lemmas"] if lemma.get("kind")}
    missing = sorted(required - kinds)
    if missing:
        feedback = (
            "The lemma chain parsed, but it is missing required square-witness "
            f"helper shapes: {missing}. Include equations equivalent to "
            "`u ◇ u = v ◇ v`, `u ◇ (v ◇ v) = u`, and `(v ◇ u) ◇ v = u`."
        )
        return {
            "round": round_idx,
            "raw_body": llm_response.get("response", ""),
            "llm_payload": llm_payload,
            "lemma_chain": chain_summary,
            "cleaned_body": "",
            "lean_code": "",
            "status": "incorrect",
            "error_code": "INCOMPLETE_LEMMA_CHAIN",
            "feedback": feedback,
            "result": {"status": "incorrect", "message": feedback},
        }

    body, chain_state = special_square_sandwich_chain_body(h_eq, g_eq)
    if body is None:
        feedback = (
            "The chain has the required helper shapes, but the square-witness "
            "renderer could not close this problem.\n\n"
            + search_state_text(chain_state, max_chars=2500)
        )
        return {
            "round": round_idx,
            "raw_body": llm_response.get("response", ""),
            "llm_payload": llm_payload,
            "lemma_chain": chain_summary,
            "cleaned_body": "",
            "lean_code": "",
            "status": "incorrect",
            "error_code": "LEMMA_CHAIN_NOT_CONSUMED",
            "feedback": feedback,
            "result": {
                "status": "incorrect",
                "error_code": "LEMMA_CHAIN_NOT_CONSUMED",
                "message": feedback,
                "chain_state": chain_state,
            },
            "module_state": chain_state,
        }

    cleaned = clean_body(body, g_eq["variables"])
    result, lean_code = verify_body(
        problem=problem,
        body=cleaned,
        lean_timeout_seconds=args.lean_timeout_seconds,
        artifact_dir=args.artifact_dir,
    )
    feedback = feedback_from_result(
        result,
        max_lines=args.max_feedback_lines,
        max_chars=args.max_feedback_chars,
    )
    result = dict(result)
    result["chain_state"] = chain_state
    return {
        "round": round_idx,
        "raw_body": llm_response.get("response", ""),
        "llm_payload": llm_payload,
        "lemma_chain": chain_summary,
        "cleaned_body": cleaned,
        "lean_code": lean_code,
        "status": result.get("status"),
        "error_code": result.get("error_code"),
        "feedback": feedback,
        "result": result,
        "module_state": chain_state,
    }


def _candidate_family_tables_for_hint(hint: dict[str, Any]) -> list[tuple[str, list[list[int]]]]:
    template = hint["template"]
    sizes = set(hint["sizes"])
    max_size = max(sizes) if sizes else 6
    rows: list[tuple[str, list[list[int]]]] = []

    def keep(route_table: Any) -> None:
        route, table = route_table
        if len(table) in sizes:
            rows.append((route, table))

    if template in {"structured", "structured_family", "existing_families", "family_sweep"}:
        for item in solver_core.structured_family_tables(max_n=max_size):
            keep(item)
    if template in {"affine", "affine_mod_n", "linear", "linear_mod_n", "existing_families", "family_sweep"}:
        for item in solver_core.affine_family_tables(max_n=max_size):
            keep(item)
    if template in {"quadratic", "quadratic_mod_n", "poly2", "existing_families", "family_sweep"}:
        for item in solver_core.quadratic_family_tables(max_n=max_size):
            keep(item)
    return rows


def _false_hint_summary(hint: dict[str, Any]) -> dict[str, Any]:
    return {
        "template": hint.get("template"),
        "sizes": hint.get("sizes"),
        "seeds": hint.get("seeds"),
        "routes": hint.get("routes"),
        "focus_cells": hint.get("focus_cells"),
        "freeze_cells": hint.get("freeze_cells"),
        "bias_cells": hint.get("bias_cells"),
        "time_budget": hint.get("time_budget"),
        "constraints": hint.get("constraints"),
        "separate_goal_at": hint.get("separate_goal_at"),
        "rationale": hint.get("rationale"),
        "has_table": hint.get("table") is not None,
    }


def _ordered_false_sizes(sizes: list[int]) -> list[int]:
    """Prefer sizes that have paid off for hard finite countermodels."""
    preferred = [6, 5, 7, 8, 4, 3, 9, 10, 11, 12, 2]
    seen: set[int] = set()
    ordered: list[int] = []
    for n in preferred + sizes:
        if n in sizes and n not in seen:
            seen.add(n)
            ordered.append(n)
    return ordered


def _local_search_jobs(sizes: list[int], seeds: list[int]) -> list[tuple[int, int]]:
    ordered_sizes = _ordered_false_sizes(sizes)
    jobs: list[tuple[int, int]] = []
    for n in ordered_sizes:
        for seed in seeds:
            jobs.append((seed, n))
    return jobs


def _local_search_jobs_from_routes(routes: list[str]) -> list[tuple[int, int]]:
    jobs: list[tuple[int, int]] = []
    seen: set[tuple[int, int]] = set()
    for route in routes:
        match = re.search(r"local_search:n=?(\d+):seed=(\d+)", route)
        if not match:
            continue
        n = int(match.group(1))
        seed = int(match.group(2))
        job = (seed, n)
        if job not in seen:
            seen.add(job)
            jobs.append(job)
    return jobs


def _model_finder_sizes_from_routes(routes: list[str]) -> list[int]:
    sizes: list[int] = []
    for route in routes:
        match = re.search(r"(?:find_model|model_finder):n(\d+)", route)
        if not match:
            continue
        n = int(match.group(1))
        if n not in sizes:
            sizes.append(n)
    return sizes


def _false_budget_remaining(args: argparse.Namespace) -> float | None:
    remaining = getattr(args, "_false_search_budget_remaining", None)
    if remaining is None:
        return None
    try:
        return max(0.0, float(remaining))
    except Exception:  # noqa: BLE001
        return None


def _charge_false_budget(args: argparse.Namespace, start_time: float, budget: float) -> float | None:
    return _charge_false_budget_spent(
        args,
        min(max(0.0, time.time() - start_time), max(0.0, budget)),
    )


def _charge_false_budget_spent(args: argparse.Namespace, spent: float) -> float | None:
    remaining = _false_budget_remaining(args)
    if remaining is None:
        return None
    new_remaining = max(0.0, remaining - spent)
    setattr(args, "_false_search_budget_remaining", new_remaining)
    return new_remaining


def _false_trial_spent(trials: list[dict[str, Any]], *, fallback_start: float, budget: float) -> float:
    spent = 0.0
    for trial in trials:
        try:
            spent += max(0.0, float(trial.get("elapsed") or 0.0))
        except Exception:  # noqa: BLE001
            continue
    if spent > 0:
        return min(spent, budget)
    return min(max(0.0, time.time() - fallback_start), budget)


def _top_cell_counts(accs: list[list[tuple[int, int]]], *, limit: int = 8) -> list[dict[str, Any]]:
    counts: dict[tuple[int, int], int] = {}
    for acc in accs:
        for cell in acc:
            counts[cell] = counts.get(cell, 0) + 1
    return [
        {"cell": [i, j], "count": count}
        for (i, j), count in sorted(counts.items(), key=lambda item: (-item[1], item[0]))[:limit]
    ]


def _false_eq_report(eq: dict[str, Any], table: list[list[int]], *, max_examples: int = 3) -> dict[str, Any]:
    n = len(table)
    variables = eq["variables"]
    total = n ** len(variables)
    violation_count = 0
    touched: list[list[tuple[int, int]]] = []
    examples: list[dict[str, Any]] = []
    for vals in itertools.product(range(n), repeat=len(variables)):
        env = dict(zip(variables, vals))
        acc: list[tuple[int, int]] = []
        lhs = solver_core._ls_trace(eq["lhs"], env, table, acc)
        rhs = solver_core._ls_trace(eq["rhs"], env, table, acc)
        if lhs != rhs:
            violation_count += 1
            touched.append(acc)
            if len(examples) < max_examples:
                examples.append({
                    "assignment": dict(zip(variables, vals)),
                    "lhs_value": lhs,
                    "rhs_value": rhs,
                    "touched_cells": [[i, j] for i, j in acc[:10]],
                })
    return {
        "violation_count": violation_count,
        "total_assignments": total,
        "violation_ratio": round(violation_count / max(1, total), 4),
        "hot_cells": _top_cell_counts(touched),
        "examples": examples,
    }


def _false_table_profile(table: list[list[int]]) -> dict[str, Any]:
    n = len(table)
    diagonal = [table[i][i] for i in range(n)]
    row_unique_counts = [len(set(row)) for row in table]
    row_constant = [i for i, row in enumerate(table) if len(set(row)) == 1]
    idempotent_count = sum(1 for i in range(n) if table[i][i] == i)
    comm_failures: list[dict[str, Any]] = []
    for i in range(n):
        for j in range(i + 1, n):
            if table[i][j] != table[j][i]:
                comm_failures.append({
                    "cell": [i, j],
                    "op_ij": table[i][j],
                    "op_ji": table[j][i],
                })
                if len(comm_failures) >= 8:
                    break
        if len(comm_failures) >= 8:
            break
    return {
        "size": n,
        "diagonal": diagonal,
        "idempotent_diagonal_count": idempotent_count,
        "row_unique_counts": row_unique_counts,
        "constant_rows": row_constant,
        "commutativity_failure_count_sampled": len(comm_failures),
        "commutativity_failure_examples": comm_failures,
    }


def _false_near_miss_interpretation(best: dict[str, Any] | None) -> str:
    if not best:
        return "local search did not keep a scored table before the budget ended"
    h_bad = int(best.get("h_violations") or 0)
    g_bad = int(best.get("g_failures") or 0)
    h_total = max(1, int(best.get("h_total_assignments") or 1))
    if h_bad == 0 and g_bad == 0:
        return "found tables satisfying H, but G still held everywhere; try a different size/template that breaks G"
    if h_bad <= max(1, h_total // 20) and g_bad > 0:
        return "G can already fail in near-models; focus the next hint on repairing the listed H-hotspot cells"
    if h_bad <= max(1, h_total // 20):
        return "H is close but G has not failed; keep the size and try fresh seeds or a G-breaking structural bias"
    if g_bad > 0:
        return "G can fail, but H is still far from repaired; try constraints targeting H-hotspot cells or switch template"
    return "neither H satisfaction nor G failure was close; try a different size, seed family, or model_finder"


def _constraint_strings(hint: dict[str, Any]) -> list[str]:
    return [
        str(item).lower()
        for item in (hint.get("constraints") or [])
        if isinstance(item, (str, int, float))
    ]


def _false_search_controls_for_size(hint: dict[str, Any], n: int) -> dict[str, Any]:
    def valid_cell(cell: Any) -> tuple[int, int] | None:
        parsed = _cell_from_value(cell)
        if parsed is None:
            return None
        i, j = parsed
        if 0 <= i < n and 0 <= j < n:
            return i, j
        return None

    focus: list[tuple[int, int]] = []
    seen: set[tuple[int, int]] = set()
    for cell in hint.get("focus_cells") or []:
        parsed = valid_cell(cell)
        if parsed is not None and parsed not in seen:
            seen.add(parsed)
            focus.append(parsed)

    freeze: dict[tuple[int, int], int] = {}
    for item in hint.get("freeze_cells") or []:
        if not isinstance(item, dict):
            continue
        parsed = valid_cell(item.get("cell"))
        values = item.get("values") if isinstance(item.get("values"), list) else []
        if parsed is None or not values:
            continue
        try:
            value = int(values[0])
        except Exception:  # noqa: BLE001
            continue
        if 0 <= value < n:
            freeze[parsed] = value

    bias: dict[tuple[int, int], list[int]] = {}
    for item in hint.get("bias_cells") or []:
        if not isinstance(item, dict):
            continue
        parsed = valid_cell(item.get("cell"))
        values = item.get("values") if isinstance(item.get("values"), list) else []
        if parsed is None:
            continue
        clean_values: list[int] = []
        for raw in values:
            try:
                value = int(raw)
            except Exception:  # noqa: BLE001
                continue
            if 0 <= value < n and value not in clean_values:
                clean_values.append(value)
        if clean_values:
            bias[parsed] = clean_values

    template = str(hint.get("template") or "")
    constraints = _constraint_strings(hint)
    enable_g_break = (
        template in {"focused_local_search", "constrained_local_search", "g_break_local_search"}
        or any("g-break" in item or "break g" in item or "g breaking" in item for item in constraints)
    )
    return {
        "focus_cells": focus,
        "freeze_cells": freeze,
        "bias_cells": bias,
        "enable_g_break": enable_g_break,
    }


def _g_touched_cells(eq: dict[str, Any], table: list[list[int]], *, limit: int = 32) -> list[tuple[int, int]]:
    n = len(table)
    cells: dict[tuple[int, int], int] = {}
    variables = eq["variables"]
    for vals in itertools.product(range(n), repeat=len(variables)):
        env = dict(zip(variables, vals))
        acc: list[tuple[int, int]] = []
        solver_core._ls_trace(eq["lhs"], env, table, acc)
        solver_core._ls_trace(eq["rhs"], env, table, acc)
        for cell in acc:
            cells[cell] = cells.get(cell, 0) + 1
    return [
        cell
        for cell, _count in sorted(cells.items(), key=lambda item: (-item[1], item[0]))[:limit]
    ]


def _partial_table_profile(table: list[list[int | None]]) -> dict[str, Any]:
    n = len(table)
    assigned = sum(1 for row in table for value in row if value is not None)
    sample_unassigned: list[list[int]] = []
    for i in range(n):
        for j in range(n):
            if table[i][j] is None and len(sample_unassigned) < 12:
                sample_unassigned.append([i, j])
    return {
        "size": n,
        "assigned_count": assigned,
        "unassigned_count": n * n - assigned,
        "assigned_ratio": round(assigned / max(1, n * n), 4),
        "row_assigned_counts": [sum(1 for value in row if value is not None) for row in table],
        "diagonal": [table[i][i] for i in range(n)],
        "sample_unassigned_cells": sample_unassigned,
    }


def _top_counter(counter: dict[tuple[int, int], int], *, limit: int = 10) -> list[dict[str, Any]]:
    return [
        {"cell": [i, j], "count": count}
        for (i, j), count in sorted(counter.items(), key=lambda item: (-item[1], item[0]))[:limit]
    ]


def _propagation_controls_for_size(hint: dict[str, Any], n: int) -> dict[str, Any]:
    controls = _false_search_controls_for_size(hint, n)
    return controls


def _mf_force_top_diag(
    side: tuple,
    env: dict[str, int],
    table: list[list[int | None]],
    val: int,
    stats: dict[str, Any],
) -> bool:
    if side[0] != "op":
        return False
    lv, lb = solver_core._mf_ev(side[1], env, table)
    if lb is not None:
        return False
    rv, rb = solver_core._mf_ev(side[2], env, table)
    if rb is not None:
        return False
    if table[lv][rv] is None:
        table[lv][rv] = val
        stats["forced_assignments"] += 1
        cell = (lv, rv)
        stats["forced_cell_counts"][cell] = stats["forced_cell_counts"].get(cell, 0) + 1
        if len(stats["forced_examples"]) < 12:
            stats["forced_examples"].append({"cell": [lv, rv], "value": val})
        return True
    return False


def _mf_propagate_diag(
    table: list[list[int | None]],
    envs1: list[dict[str, int]],
    lhs: tuple,
    rhs: tuple,
    stats: dict[str, Any],
) -> bool:
    changed = True
    while changed:
        changed = False
        stats["propagation_passes"] += 1
        for env in envs1:
            av, ab = solver_core._mf_ev(lhs, env, table)
            bv, bb = solver_core._mf_ev(rhs, env, table)
            for block in (ab, bb):
                if block is not None:
                    stats["blocked_cell_counts"][block] = stats["blocked_cell_counts"].get(block, 0) + 1
            if ab is None and bb is None:
                if av != bv:
                    stats["conflicts"] += 1
                    if len(stats["conflict_examples"]) < 8:
                        stats["conflict_examples"].append({
                            "assignment": dict(env),
                            "lhs_value": av,
                            "rhs_value": bv,
                        })
                    return False
            elif ab is None:
                if _mf_force_top_diag(rhs, env, table, av, stats):
                    changed = True
            elif bb is None:
                if _mf_force_top_diag(lhs, env, table, bv, stats):
                    changed = True
    return True


def _partial_eq2_violations(eq: dict[str, Any], table: list[list[int | None]], *, max_examples: int = 4) -> dict[str, Any]:
    n = len(table)
    variables = eq["variables"]
    determined = 0
    violations = 0
    examples: list[dict[str, Any]] = []
    hot: dict[tuple[int, int], int] = {}
    for vals in itertools.product(range(n), repeat=len(variables)):
        env = dict(zip(variables, vals))
        acc: list[tuple[int, int]] = []
        av, ab = solver_core._mf_ev(eq["lhs"], env, table)
        bv, bb = solver_core._mf_ev(eq["rhs"], env, table)
        if ab is None and bb is None:
            determined += 1
            if av != bv:
                violations += 1
                if len(examples) < max_examples:
                    solver_core._ls_trace(eq["lhs"], env, table, acc)
                    solver_core._ls_trace(eq["rhs"], env, table, acc)
                    examples.append({
                        "assignment": dict(env),
                        "lhs_value": av,
                        "rhs_value": bv,
                        "touched_cells": [[i, j] for i, j in acc[:10]],
                    })
                for cell in acc:
                    hot[cell] = hot.get(cell, 0) + 1
    return {
        "determined_assignments": determined,
        "determined_violations": violations,
        "examples": examples,
        "hot_cells": _top_counter(hot),
    }


def _diagnostic_find_model(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    *,
    n: int,
    time_budget: float,
    node_cap: int,
    hint: dict[str, Any],
) -> tuple[str, list[list[int]] | None, dict[str, Any]]:
    envs1 = [dict(zip(h_eq["variables"], v)) for v in itertools.product(range(n), repeat=len(h_eq["variables"]))]
    envs2 = [dict(zip(g_eq["variables"], v)) for v in itertools.product(range(n), repeat=len(g_eq["variables"]))]
    deadline = time.monotonic() + time_budget
    controls = _propagation_controls_for_size(hint, n)
    focus_cells = set(controls["focus_cells"])
    freeze_cells: dict[tuple[int, int], int] = controls["freeze_cells"]
    bias_cells: dict[tuple[int, int], list[int]] = controls["bias_cells"]
    stats: dict[str, Any] = {
        "nodes": 0,
        "node_cap": node_cap,
        "status": "none",
        "forced_assignments": 0,
        "propagation_passes": 0,
        "conflicts": 0,
        "forced_cell_counts": {},
        "blocked_cell_counts": {},
        "branch_cell_counts": {},
        "forced_examples": [],
        "conflict_examples": [],
    }
    best_partial: dict[str, Any] | None = None

    def assigned_count(table: list[list[int | None]]) -> int:
        return sum(1 for row in table for value in row if value is not None)

    def update_best(table: list[list[int | None]], *, reason: str) -> None:
        nonlocal best_partial
        profile = _partial_table_profile(table)
        eq2_report = _partial_eq2_violations(g_eq, table)
        score = (
            int(eq2_report["determined_violations"]),
            int(profile["assigned_count"]),
        )
        old_score = None if best_partial is None else (
            int(best_partial.get("eq2_partial", {}).get("determined_violations") or 0),
            int(best_partial.get("profile", {}).get("assigned_count") or 0),
        )
        if old_score is not None and score <= old_score:
            return
        best_partial = {
            "reason": reason,
            "profile": profile,
            "eq2_partial": eq2_report,
        }

    def violates_eq2(table: list[list[int | None]]) -> bool:
        for env in envs2:
            av, ab = solver_core._mf_ev(g_eq["lhs"], env, table)
            bv, bb = solver_core._mf_ev(g_eq["rhs"], env, table)
            if ab is None and bb is None and av != bv:
                return True
        return False

    def pick_cell(table: list[list[int | None]]) -> tuple[int, int] | None:
        for cell in sorted(focus_cells):
            i, j = cell
            if table[i][j] is None:
                return cell
        for env in envs1:
            for side in (h_eq["lhs"], h_eq["rhs"]):
                _value, block = solver_core._mf_ev(side, env, table)
                if block is not None and table[block[0]][block[1]] is None:
                    return block
        for i in range(n):
            for j in range(n):
                if table[i][j] is None:
                    return i, j
        return None

    def values_for(cell: tuple[int, int]) -> list[int]:
        values = bias_cells.get(cell) or []
        values = [value for value in values if 0 <= value < n]
        return values + [value for value in range(n) if value not in values]

    def search(table: list[list[int | None]], depth: int = 0) -> list[list[int]] | None:
        if time.monotonic() > deadline or stats["nodes"] >= node_cap:
            stats["status"] = "budget"
            return None
        stats["nodes"] += 1
        t2 = [row[:] for row in table]
        if not _mf_propagate_diag(t2, envs1, h_eq["lhs"], h_eq["rhs"], stats):
            update_best(t2, reason="conflict_after_propagation")
            return None
        update_best(t2, reason="after_propagation")
        cell = pick_cell(t2)
        if cell is None:
            if violates_eq2(t2):
                stats["status"] = "found"
                return [[int(value) for value in row] for row in t2]
            return None
        stats["branch_cell_counts"][cell] = stats["branch_cell_counts"].get(cell, 0) + 1
        i, j = cell
        for value in values_for(cell):
            t2[i][j] = value
            result = search(t2, depth + 1)
            if result is not None:
                return result
            if stats["status"] == "budget":
                return None
            t2[i][j] = None
        return None

    initial: list[list[int | None]] = [[None] * n for _ in range(n)]
    initial_conflict = False
    for (i, j), value in freeze_cells.items():
        if initial[i][j] is not None and initial[i][j] != value:
            initial_conflict = True
        initial[i][j] = value
    result = None if initial_conflict else search(initial)
    status = "found" if result is not None else ("budget" if stats["status"] == "budget" else "none")
    diag = {
        "kind": "propagation_model_finder_diagnostics",
        "size": n,
        "status": status,
        "nodes": stats["nodes"],
        "node_cap": node_cap,
        "forced_assignments": stats["forced_assignments"],
        "propagation_passes": stats["propagation_passes"],
        "conflicts": stats["conflicts"],
        "forced_cells": _top_counter(stats["forced_cell_counts"]),
        "blocked_cells": _top_counter(stats["blocked_cell_counts"]),
        "branch_cells": _top_counter(stats["branch_cell_counts"]),
        "forced_examples": stats["forced_examples"],
        "conflict_examples": stats["conflict_examples"],
        "best_partial": best_partial,
        "initial_constraints": {
            "freeze_cells": [{"cell": [i, j], "value": value} for (i, j), value in sorted(freeze_cells.items())],
            "focus_cells": [[i, j] for i, j in sorted(focus_cells)],
            "bias_cell_count": len(bias_cells),
            "initial_conflict": initial_conflict,
        },
    }
    return status, result, diag


def _diagnostic_local_search_ce(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    *,
    sizes: tuple[int, ...],
    time_budget: float,
    seed: int,
    hint: dict[str, Any] | None = None,
) -> tuple[tuple[int, list[list[int]], str] | None, dict[str, Any]]:
    rng = random.Random(seed)
    per = time_budget / max(1, len(sizes))
    hv = h_eq["variables"]
    best: dict[str, Any] | None = None
    best_g_break: dict[str, Any] | None = None
    per_size: list[dict[str, Any]] = []

    def consider_table(n: int, table: list[list[int]], h_violated: list[list[tuple[int, int]]], reason: str) -> None:
        nonlocal best, best_g_break
        h_count = len(h_violated)
        h_total = n ** len(hv)
        snapshot: dict[str, Any] = {
            "size": n,
            "reason": reason,
            "h_violations": h_count,
            "h_total_assignments": h_total,
            "h_violation_ratio": round(h_count / max(1, h_total), 4),
            "h_hot_cells": _top_cell_counts(h_violated),
            "_table": [row[:] for row in table],
        }

        near_h_threshold = max(3, h_total // 50)
        if h_count <= near_h_threshold:
            g_report = _false_eq_report(g_eq, table, max_examples=0)
            snapshot.update({
                "g_failures": g_report["violation_count"],
                "g_total_assignments": g_report["total_assignments"],
                "g_failure_ratio": g_report["violation_ratio"],
                "g_failure_hot_cells": g_report["hot_cells"],
            })
            if g_report["violation_count"] > 0:
                old_g_score = None if best_g_break is None else (
                    int(best_g_break.get("g_failures") or 0),
                    -int(best_g_break.get("h_violations") or 0),
                )
                new_g_score = (int(g_report["violation_count"]), -h_count)
                if old_g_score is None or new_g_score > old_g_score:
                    best_g_break = dict(snapshot)

        old_h_count = None if best is None else int(best.get("h_violations") or 0)
        if old_h_count is None or h_count < old_h_count:
            best = snapshot

    def finalize_snapshot(snapshot: dict[str, Any] | None) -> dict[str, Any] | None:
        if snapshot is None:
            return None
        final = dict(snapshot)
        table = final.pop("_table", None)
        if not isinstance(table, list):
            return final
        if final.get("g_failures") is None:
            g_report = _false_eq_report(g_eq, table, max_examples=2)
            final.update({
                "g_failures": g_report["violation_count"],
                "g_total_assignments": g_report["total_assignments"],
                "g_failure_ratio": g_report["violation_ratio"],
                "g_failure_hot_cells": g_report["hot_cells"],
                "g_failure_examples": g_report["examples"],
            })
        else:
            g_report = _false_eq_report(g_eq, table, max_examples=2)
            final["g_failure_examples"] = g_report["examples"]
            if not final.get("g_failure_hot_cells"):
                final["g_failure_hot_cells"] = g_report["hot_cells"]
        h_report = _false_eq_report(h_eq, table, max_examples=2)
        final.update({
            "h_failure_examples": h_report["examples"],
            "table_profile": _false_table_profile(table),
        })
        return final

    def finalize_best() -> dict[str, Any] | None:
        return finalize_snapshot(best)

    for n in sizes:
        controls = _false_search_controls_for_size(hint or {}, n)
        focus_cells = set(controls["focus_cells"])
        freeze_cells: dict[tuple[int, int], int] = controls["freeze_cells"]
        bias_cells: dict[tuple[int, int], list[int]] = controls["bias_cells"]
        enable_g_break = bool(controls["enable_g_break"])

        def apply_freeze(table: list[list[int]]) -> None:
            for (i, j), value in freeze_cells.items():
                table[i][j] = value

        def choose_value(cell: tuple[int, int], old: int | None = None) -> int:
            values = bias_cells.get(cell) or []
            if values and rng.random() < 0.75:
                choices = [value for value in values if value != old] or values
                return rng.choice(choices)
            if old is None:
                return rng.randrange(n)
            if n <= 1:
                return old
            value = rng.randrange(n)
            if value == old:
                value = (value + 1) % n
            return value

        deadline = time.monotonic() + per
        triples = list(itertools.product(range(n), repeat=len(hv)))
        size_attempts = 0
        size_best_start = best
        while time.monotonic() < deadline:
            size_attempts += 1
            tab = [[rng.randrange(n) for _ in range(n)] for _ in range(n)]
            apply_freeze(tab)
            g_breaks = 0
            for step in range(4000):
                if time.monotonic() > deadline:
                    break
                violated: list[list[tuple[int, int]]] = []
                for vals in triples:
                    env = dict(zip(hv, vals))
                    acc: list[tuple[int, int]] = []
                    if solver_core._ls_trace(h_eq["lhs"], env, tab, acc) != solver_core._ls_trace(h_eq["rhs"], env, tab, acc):
                        violated.append(acc)
                if step == 0 or not violated or best is None or len(violated) < int(best.get("h_violations") or 10**9):
                    consider_table(n, tab, violated, reason=f"step={step}")
                if not violated:
                    if solver_core.is_counterexample(h_eq, g_eq, tab):
                        final_best = finalize_best()
                        final_g_break = finalize_snapshot(best_g_break)
                        diag = {
                            "kind": "local_search_diagnostics",
                            "seed": seed,
                            "sizes": list(sizes),
                            "best_near_miss": final_best,
                            "alternate_near_misses": [final_g_break] if final_g_break else [],
                            "per_size": per_size,
                            "interpretation": "found countermodel",
                        }
                        return (n, tab, f"localsearch:fin{n}"), diag
                    if enable_g_break and g_breaks < 8:
                        g_cells = list(focus_cells) or _g_touched_cells(g_eq, tab)
                        mutable = [cell for cell in g_cells if cell not in freeze_cells]
                        if mutable:
                            for _ in range(min(3, len(mutable))):
                                a, b = rng.choice(mutable)
                                tab[a][b] = choose_value((a, b), tab[a][b])
                            apply_freeze(tab)
                            g_breaks += 1
                            continue
                    break
                cand = list(set(rng.choice(violated)))
                cand = [cell for cell in cand if cell not in freeze_cells]
                if focus_cells:
                    focused = [cell for cell in cand if cell in focus_cells]
                    if focused and rng.random() < 0.75:
                        cand = focused
                    elif not focused and rng.random() < 0.25:
                        cand = [cell for cell in focus_cells if cell not in freeze_cells] + cand
                if not cand:
                    break
                if rng.random() < 0.3:
                    a, b = rng.choice(cand)
                    tab[a][b] = choose_value((a, b), tab[a][b])
                    apply_freeze(tab)
                else:
                    best_flip = None
                    for (a, b) in cand:
                        if (a, b) in freeze_cells:
                            continue
                        old = tab[a][b]
                        values = bias_cells.get((a, b)) or list(range(n))
                        for val in values:
                            if val == old:
                                continue
                            tab[a][b] = val
                            apply_freeze(tab)
                            v = sum(
                                1
                                for vs in triples
                                if solver_core._ls_trace(h_eq["lhs"], dict(zip(hv, vs)), tab, [])
                                != solver_core._ls_trace(h_eq["rhs"], dict(zip(hv, vs)), tab, [])
                            )
                            if best_flip is None or v < best_flip[0]:
                                    best_flip = (v, a, b, val)
                        tab[a][b] = old
                        apply_freeze(tab)
                    if best_flip is None:
                        break
                    _, a, b, val = best_flip
                    tab[a][b] = val
                    apply_freeze(tab)
        per_size.append({
            "size": n,
            "attempts": size_attempts,
            "best_changed": best is not size_best_start,
            "best_h_violations_after_size": None if best is None else best.get("h_violations"),
            "best_g_failures_after_size": None if best is None else best.get("g_failures"),
            "focused_controls": {
                "focus_cells": [[i, j] for i, j in sorted(focus_cells)],
                "freeze_cell_count": len(freeze_cells),
                "bias_cell_count": len(bias_cells),
                "enable_g_break": enable_g_break,
            },
        })

    final_best = finalize_best()
    final_g_break = finalize_snapshot(best_g_break)
    diag = {
        "kind": "local_search_diagnostics",
        "seed": seed,
        "sizes": list(sizes),
        "best_near_miss": final_best,
        "alternate_near_misses": [final_g_break] if final_g_break else [],
        "per_size": per_size,
        "interpretation": _false_near_miss_interpretation(final_best),
    }
    return None, diag


def _planned_false_routes(hint: dict[str, Any], *, budget: float) -> list[str]:
    template = hint.get("template")
    sizes = hint.get("sizes") or []
    seeds = hint.get("seeds") or [0]
    routes = hint.get("routes") or []
    if routes:
        return [str(route) for route in routes]
    if template in {
        "local_search",
        "focused_local_search",
        "constrained_local_search",
        "g_break_local_search",
        "walksat",
        "random_repair",
        "quasigroup_or_loop",
        "latin_square",
        "permutation",
        "loop",
    }:
        if len(sizes) > 1 and budget >= 15.0:
            return [f"local_search:sizes={list(sizes)}:seed={seed}" for seed in seeds]
        return [f"local_search:n={n}:seed={seed}" for seed, n in _local_search_jobs(sizes, seeds)]
    if template in {"model_finder", "backtracking", "propagation", "propagating_model_finder", "generic_table"}:
        routes = hint.get("routes") or []
        if routes:
            planned = []
            for n in _model_finder_sizes_from_routes(routes):
                planned.append(f"find_model:n{n}")
            if planned:
                return planned
        return [f"find_model:n{n}" for n in sizes]
    return []


def _false_need_hint(
    hint: dict[str, Any],
    trials: list[dict[str, Any]],
    *,
    budget: float,
    budget_remaining: float | None,
) -> dict[str, Any]:
    routes = [str(trial.get("route")) for trial in trials if trial.get("route")]
    planned_routes = _planned_false_routes(hint, budget=budget)
    untried_routes = [route for route in planned_routes if route not in routes]
    missed_by_size: dict[str, list[int]] = {}
    near_misses: list[dict[str, Any]] = []
    propagation_diagnostics: list[dict[str, Any]] = []
    for trial in trials:
        route = str(trial.get("route") or "")
        if trial.get("status") == "found":
            continue
        diag = _as_dict(trial.get("diagnostics"))
        if diag.get("kind") == "propagation_model_finder_diagnostics":
            best_partial = _as_dict(diag.get("best_partial"))
            profile = _as_dict(best_partial.get("profile"))
            eq2_partial = _as_dict(best_partial.get("eq2_partial"))
            propagation_diagnostics.append({
                "route": route,
                "status": trial.get("status"),
                "size": diag.get("size"),
                "nodes": diag.get("nodes"),
                "node_cap": diag.get("node_cap"),
                "forced_assignments": diag.get("forced_assignments"),
                "conflicts": diag.get("conflicts"),
                "forced_cells": diag.get("forced_cells"),
                "blocked_cells": diag.get("blocked_cells"),
                "branch_cells": diag.get("branch_cells"),
                "best_partial_assigned_ratio": profile.get("assigned_ratio"),
                "best_partial_unassigned_count": profile.get("unassigned_count"),
                "best_partial_eq2_violations": eq2_partial.get("determined_violations"),
                "best_partial_eq2_determined": eq2_partial.get("determined_assignments"),
                "initial_constraints": diag.get("initial_constraints"),
            })
        best = _as_dict(diag.get("best_near_miss"))
        candidates = [best] if best else []
        for alternate in diag.get("alternate_near_misses") or []:
            if isinstance(alternate, dict):
                candidates.append(alternate)
        for candidate in candidates:
            if not candidate:
                continue
            near_misses.append({
                "route": route,
                "interpretation": diag.get("interpretation"),
                "size": candidate.get("size"),
                "h_violations": candidate.get("h_violations"),
                "h_total_assignments": candidate.get("h_total_assignments"),
                "h_violation_ratio": candidate.get("h_violation_ratio"),
                "g_failures": candidate.get("g_failures"),
                "g_total_assignments": candidate.get("g_total_assignments"),
                "g_failure_ratio": candidate.get("g_failure_ratio"),
                "h_hot_cells": candidate.get("h_hot_cells"),
                "g_failure_hot_cells": candidate.get("g_failure_hot_cells"),
                "table_profile": candidate.get("table_profile"),
            })
        seed_match = re.search(r"seed=(\d+)", route)
        size_match = re.search(r"n=(\d+)", route)
        if size_match and seed_match:
            missed_by_size.setdefault(size_match.group(1), []).append(int(seed_match.group(1)))
    near_misses = sorted(
        near_misses,
        key=lambda item: (
            int(item.get("h_violations") if item.get("h_violations") is not None else 10**9),
            -int(item.get("g_failures") if item.get("g_failures") is not None else 0),
        ),
    )[:4]
    suggestions = [
        "Do not repeat an already tried route exactly.",
        "If useful requested routes were not reached because the slice ended, return a narrower hint containing only those untried routes.",
        "If a near miss has low H violations and nonzero G failures, propose constraints that repair H-hotspot cells while preserving the G failure.",
        "If propagation reports many blocked or branch cells, try focus_cells/bias_cells on those cells or a narrower find_model route.",
        "If local_search missed, try fresh seeds on the most plausible size or switch to model_finder / existing_families.",
        "If the same size keeps missing, propose a structural constraint or a different carrier size.",
    ]
    return {
        "need_hint": "propose a different finite-countermodel search hint",
        "last_template": hint.get("template"),
        "last_sizes": hint.get("sizes"),
        "last_seeds": hint.get("seeds"),
        "avoid_routes": routes[-12:],
        "untried_requested_routes": untried_routes[:12],
        "missed_local_search_seeds_by_size": missed_by_size,
        "best_near_misses": near_misses,
        "propagation_diagnostics": propagation_diagnostics[:4],
        "budget_remaining": budget_remaining,
        "suggestions": suggestions,
    }


def verify_false_hint(
    *,
    args: argparse.Namespace,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    hint: dict[str, Any],
) -> tuple[dict[str, Any], str]:
    start_time = time.time()
    template = hint["template"]
    requested_budget = float(hint["time_budget"] or args.false_search_budget)
    budget_cap = float(args.false_search_budget or requested_budget)
    total_remaining = _false_budget_remaining(args)
    if total_remaining is not None:
        budget_cap = min(budget_cap, total_remaining)
    if budget_cap <= 0:
        need_hint = _false_need_hint(hint, trials=[], budget=0.0, budget_remaining=0.0)
        return {
            "status": "incorrect",
            "error_code": "FALSE_TOTAL_SEARCH_BUDGET_EXHAUSTED",
            "message": (
                "The fixed false-side search budget is exhausted. The next LLM "
                "hint must use information already in the transcript, not more "
                "countermodel search."
            ),
            "verdict": "false",
            "hint": _false_hint_summary(hint),
            "search_trials": [],
            "budget_seconds": 0.0,
            "budget_remaining": 0.0,
            "need_hint": need_hint,
        }, ""
    budget = max(0.5, min(requested_budget, budget_cap))
    sizes = hint["sizes"] or [5, 6]
    seeds = hint["seeds"] or [0]
    trials: list[dict[str, Any]] = []

    def verify_found(table: list[list[int]], route: str) -> tuple[dict[str, Any], str]:
        result, code = verify_false_table(
            problem=problem,
            h_eq=h_eq,
            g_eq=g_eq,
            table=table,
            lean_timeout_seconds=args.lean_timeout_seconds,
            artifact_dir=args.artifact_dir,
        )
        result = dict(result)
        result["false_model_source"] = route
        result["counterexample_size"] = len(table)
        result["counterexample_table"] = table
        result["search_trials"] = trials
        result["budget_seconds"] = budget
        spent = _false_trial_spent(trials, fallback_start=start_time, budget=budget)
        result["search_budget_spent"] = spent
        result["budget_remaining"] = _charge_false_budget_spent(args, spent)
        return result, code

    if hint.get("table") is not None:
        table = hint["table"]
        result, code = verify_false_table(
            problem=problem,
            h_eq=h_eq,
            g_eq=g_eq,
            table=table,
            lean_timeout_seconds=args.lean_timeout_seconds,
            artifact_dir=args.artifact_dir,
        )
        result = dict(result)
        result["false_model_source"] = "llm_full_table"
        result["counterexample_size"] = len(table) if isinstance(table, list) else None
        result["counterexample_table"] = table
        result["search_trials"] = trials
        result["budget_seconds"] = budget
        result["search_budget_spent"] = 0.0
        result["budget_remaining"] = _false_budget_remaining(args)
        return result, code

    if template in {
        "structured",
        "structured_family",
        "affine",
        "affine_mod_n",
        "linear",
        "linear_mod_n",
        "quadratic",
        "quadratic_mod_n",
        "poly2",
        "existing_families",
        "family_sweep",
    }:
        for route, table in _candidate_family_tables_for_hint(hint):
            if time.time() - start_time > budget:
                trials.append({"route": route, "status": "budget"})
                break
            ok = solver_core.is_counterexample(h_eq, g_eq, table)
            trials.append({"route": route, "status": "counterexample" if ok else "not_counterexample", "n": len(table)})
            if ok:
                return verify_found(table, route)

    if template in {"model_finder", "backtracking", "propagation", "propagating_model_finder", "generic_table"}:
        route_sizes = _model_finder_sizes_from_routes(hint.get("routes") or [])
        model_sizes = route_sizes or sizes
        per = max(0.5, budget / max(1, len(model_sizes)))
        for n in model_sizes:
            if time.time() - start_time > budget:
                break
            t0 = time.time()
            status, table, diag = _diagnostic_find_model(
                h_eq,
                g_eq,
                n=n,
                time_budget=min(per, max(0.5, budget - (time.time() - start_time))),
                node_cap=args.false_node_cap,
                hint=hint,
            )
            trials.append({
                "route": f"find_model:n{n}",
                "status": status,
                "elapsed": round(time.time() - t0, 3),
                "diagnostics": diag,
            })
            if status == "found" and table is not None:
                return verify_found(table, f"find_model:n{n}")

    if template in {
        "local_search",
        "focused_local_search",
        "constrained_local_search",
        "g_break_local_search",
        "walksat",
        "random_repair",
        "quasigroup_or_loop",
        "latin_square",
        "permutation",
        "loop",
    }:
        route_jobs = _local_search_jobs_from_routes(hint.get("routes") or [])
        used_priority_scheduler = False
        if route_jobs:
            used_priority_scheduler = True
            jobs = route_jobs
            per = max(1.0, budget / max(1, len(jobs)))
            for seed, n in jobs:
                if time.time() - start_time > budget:
                    break
                t0 = time.time()
                remaining = budget - (time.time() - start_time)
                ce, diag = _diagnostic_local_search_ce(
                    h_eq,
                    g_eq,
                    sizes=(n,),
                    time_budget=min(per, max(1.0, remaining)),
                    seed=seed,
                    hint=hint,
                )
                trial = {
                    "route": f"local_search:n={n}:seed={seed}",
                    "status": "found" if ce else "no_model",
                    "elapsed": round(time.time() - t0, 3),
                    "diagnostics": diag,
                }
                if ce:
                    n, table, route = ce
                    trial["n"] = n
                    trial["source"] = route
                    trials.append(trial)
                    return verify_found(table, f"{route}:seed={seed}")
                trials.append(trial)

        elif len(sizes) > 1 and budget >= 15.0:
            used_priority_scheduler = True
            jobs = [(seed, tuple(sizes)) for seed in seeds]
            per = max(4.0, budget / max(1, len(jobs)))
            for seed, size_tuple in jobs:
                if time.time() - start_time > budget:
                    break
                t0 = time.time()
                remaining = budget - (time.time() - start_time)
                ce, diag = _diagnostic_local_search_ce(
                    h_eq,
                    g_eq,
                    sizes=size_tuple,
                    time_budget=min(per, max(1.0, remaining)),
                    seed=seed,
                    hint=hint,
                )
                trial = {
                    "route": f"local_search:sizes={list(size_tuple)}:seed={seed}",
                    "status": "found" if ce else "no_model",
                    "elapsed": round(time.time() - t0, 3),
                    "diagnostics": diag,
                }
                if ce:
                    n, table, route = ce
                    trial["n"] = n
                    trial["source"] = route
                    trials.append(trial)
                    return verify_found(table, f"{route}:seed={seed}")
                trials.append(trial)

        if not used_priority_scheduler:
            jobs = _local_search_jobs(sizes, seeds)
            min_slice = 4.0 if len(sizes) > 1 else 1.0
            per = max(min_slice, budget / max(1, len(jobs)))
            for seed, n in jobs:
                if time.time() - start_time > budget:
                    break
                t0 = time.time()
                remaining = budget - (time.time() - start_time)
                ce, diag = _diagnostic_local_search_ce(
                    h_eq,
                    g_eq,
                    sizes=(n,),
                    time_budget=min(per, max(1.0, remaining)),
                    seed=seed,
                    hint=hint,
                )
                trial = {
                    "route": f"local_search:n={n}:seed={seed}",
                    "status": "found" if ce else "no_model",
                    "elapsed": round(time.time() - t0, 3),
                    "diagnostics": diag,
                }
                if ce:
                    n, table, route = ce
                    trial["n"] = n
                    trial["source"] = route
                    trials.append(trial)
                    return verify_found(table, f"{route}:seed={seed}")
                trials.append(trial)

    feedback = (
        "No countermodel was found from this false_model_hint within the sidecar "
        "budget. Try changing carrier size, seeds, or template. For hard false "
        "cases where n<=4 has no model, useful next hints often try n=5..8 with "
        "`local_search` or a stronger structural template."
    )
    spent = _false_trial_spent(trials, fallback_start=start_time, budget=budget)
    budget_remaining = _charge_false_budget_spent(args, spent)
    need_hint = _false_need_hint(hint, trials, budget=budget, budget_remaining=budget_remaining)
    return {
        "status": "incorrect",
        "error_code": "FALSE_HINT_NO_MODEL",
        "message": feedback,
        "verdict": "false",
        "hint": _false_hint_summary(hint),
        "search_trials": trials,
        "budget_seconds": budget,
        "search_budget_spent": spent,
        "budget_remaining": budget_remaining,
        "need_hint": need_hint,
        "elapsed": round(time.time() - start_time, 3),
    }, ""


def _hint_response_from_tool_call(tool_call: dict[str, Any], *, kind: str) -> dict[str, Any]:
    payload = dict(_as_dict(tool_call.get("raw")))
    payload["kind"] = kind
    if "seed_h_args" not in payload and isinstance(payload.get("seed_h_args_template"), list):
        payload["seed_h_args"] = payload["seed_h_args_template"]
    if kind == "lemma_hint" and isinstance(payload.get("lemmas"), list):
        shared_seed_h_args = payload.get("seed_h_args")
        shared_use_args = payload.get("use_args")
        if shared_seed_h_args is not None or shared_use_args is not None:
            normalized_lemmas: list[Any] = []
            for item in payload["lemmas"]:
                if isinstance(item, str):
                    lemma_item: dict[str, Any] = {"equation": item}
                elif isinstance(item, dict):
                    lemma_item = dict(item)
                else:
                    normalized_lemmas.append(item)
                    continue
                if shared_seed_h_args is not None and "seed_h_args" not in lemma_item:
                    lemma_item["seed_h_args"] = shared_seed_h_args
                if shared_use_args is not None and "use_args" not in lemma_item:
                    lemma_item["use_args"] = shared_use_args
                normalized_lemmas.append(lemma_item)
            payload["lemmas"] = normalized_lemmas
    for key in ("tool", "target", "budget", "time_budget", "budget_seconds", "why", "rationale"):
        payload.pop(key, None)
    return {
        "response": json.dumps(payload, ensure_ascii=False),
        "source": f"tool_call_adapter:{kind}",
    }


def _false_hint_response_from_tool_call(tool_call: dict[str, Any]) -> dict[str, Any]:
    payload = dict(_as_dict(tool_call.get("raw")))
    payload["kind"] = "false_model_hint"
    original_tool = str(payload.get("tool") or tool_call.get("tool") or "")
    if not payload.get("template"):
        if "focused" in original_tool:
            payload["template"] = "focused_local_search"
        elif "model_finder" in original_tool or "propagation" in original_tool:
            payload["template"] = "model_finder"
        else:
            payload["template"] = "local_search"
    if not payload.get("time_budget"):
        payload["time_budget"] = tool_call.get("budget") or payload.get("budget") or payload.get("budget_seconds")
    if not payload.get("rationale") and tool_call.get("why"):
        payload["rationale"] = tool_call["why"]
    for key in ("tool", "target", "budget", "budget_seconds", "why"):
        payload.pop(key, None)
    return {
        "response": json.dumps(payload, ensure_ascii=False),
        "source": "tool_call_adapter:false_model_search",
    }


def _recent_seed_h_arg_rows(
    previous: list[dict[str, Any]] | None,
    *,
    limit: int = 8,
) -> list[list[str]]:
    rows: list[list[str]] = []
    seen: set[tuple[str, ...]] = set()

    def add_row(raw_row: Any) -> None:
        if not isinstance(raw_row, list):
            return
        row = [str(item).strip() for item in raw_row if str(item).strip()]
        if not row:
            return
        key = tuple(row)
        if key in seen:
            return
        seen.add(key)
        rows.append(row)

    def scan_templates(raw_templates: Any) -> None:
        if not isinstance(raw_templates, list):
            return
        for template in raw_templates:
            if not isinstance(template, dict):
                continue
            raw_rows = template.get("seed_h_args") or template.get("seed_h_args_template")
            if isinstance(raw_rows, list):
                for raw_row in raw_rows:
                    add_row(raw_row)

    for attempt in reversed(previous or []):
        module_state = _as_dict(attempt.get("module_state"))
        generated = module_state.get("generated_h_args")
        if isinstance(generated, list):
            for item in generated:
                if isinstance(item, dict):
                    add_row(item.get("args"))

        need_hint = _as_dict(module_state.get("need_hint"))
        scan_templates(need_hint.get("llm_tool_call_templates"))

        if len(rows) >= limit:
            break

    return rows[:limit]


def _tool_attempt_from_delegated_false_model(
    *,
    round_idx: int | str,
    llm_response: dict[str, Any],
    llm_payload: dict[str, Any],
    tool: str,
    target: str,
    tool_call: dict[str, Any],
    delegated: dict[str, Any],
) -> dict[str, Any]:
    module_state = dict(_as_dict(delegated.get("module_state")))
    need_hint = dict(_as_dict(module_state.get("need_hint")))
    if need_hint and "llm_tool_call_templates" not in need_hint:
        routes = need_hint.get("untried_requested_routes") or []
        if routes:
            template = {
                "kind": "tool_call",
                "tool": "false_model_search",
                "target": "goal",
                "template": "focused_local_search",
                "routes": routes[:4],
                "focus_cells": need_hint.get("focus_cells") or [],
                "budget": min(float(tool_call.get("budget") or 6.0), 8.0),
                "why": "Continue only the useful false-search routes that were requested but not reached.",
            }
        else:
            template = {
                "kind": "tool_call",
                "tool": "false_model_search",
                "target": "goal",
                "template": "local_search",
                "sizes": need_hint.get("last_sizes") or [5, 6],
                "seeds": [0, 1, 2, 3],
                "budget": min(float(tool_call.get("budget") or 6.0), 8.0),
                "why": "Try a narrow finite-countermodel search based on the previous near misses.",
            }
        need_hint["llm_tool_call_templates"] = [template]
    module_state.update({
        "kind": "false_model_search_tool",
        "tool": tool,
        "target": target,
        "adapter": "tool_call",
        "status": delegated.get("status"),
        "error_code": delegated.get("error_code"),
        "need_hint": need_hint or module_state.get("need_hint"),
    })
    result = dict(_as_dict(delegated.get("result")) or {
        "status": delegated.get("status"),
        "error_code": delegated.get("error_code"),
        "message": delegated.get("feedback", ""),
    })
    result["module_state"] = module_state
    return {
        "round": round_idx,
        "raw_body": llm_response.get("response", ""),
        "llm_payload": llm_payload,
        "delegated_payload": delegated.get("llm_payload"),
        "tool_call": {
            "tool": tool,
            "target": target,
            "template": _as_dict(tool_call.get("raw")).get("template"),
            "sizes": _as_dict(tool_call.get("raw")).get("sizes") or _as_dict(tool_call.get("raw")).get("carrier_size"),
            "seeds": _as_dict(tool_call.get("raw")).get("seeds") or _as_dict(tool_call.get("raw")).get("seed"),
            "routes": _as_dict(tool_call.get("raw")).get("routes"),
            "budget": tool_call.get("budget"),
            "why": tool_call.get("why"),
        },
        "false_model_hint": delegated.get("false_model_hint"),
        "candidate_summaries": delegated.get("candidate_summaries"),
        "cleaned_body": delegated.get("cleaned_body", ""),
        "lean_code": delegated.get("lean_code", ""),
        "status": delegated.get("status"),
        "error_code": delegated.get("error_code"),
        "feedback": delegated.get("feedback", ""),
        "result": result,
        "module_state": module_state,
    }


def _tool_attempt_from_delegated_hint(
    *,
    round_idx: int | str,
    llm_response: dict[str, Any],
    llm_payload: dict[str, Any],
    tool: str,
    target: str,
    tool_call: dict[str, Any],
    delegated: dict[str, Any],
    previous: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    module_state = _as_dict(delegated.get("module_state"))
    if module_state:
        module_state = {
            **module_state,
            "tool": tool,
            "target": target,
            "adapter": "tool_call",
        }
    else:
        search_state = _as_dict(delegated.get("search_state"))
        bridge_hint = _as_dict(search_state.get("need_hint"))
        candidate_summaries = [
            item for item in (delegated.get("candidate_summaries") or [])
            if isinstance(item, dict)
        ]
        proved_unused = [
            item for item in candidate_summaries
            if _as_dict(item.get("lemma_lifecycle")).get("proved")
            and not _as_dict(item.get("lemma_lifecycle")).get("used_for_goal")
        ]
        seed_h_args = _recent_seed_h_arg_rows(previous)
        llm_templates: list[dict[str, Any]] = []
        if bridge_hint.get("left_term") and bridge_hint.get("right_term"):
            llm_templates.append({
                "kind": "tool_call",
                "tool": "lemma_hint",
                "target": "goal",
                "lemmas": [
                    f"{bridge_hint['left_term']} = {bridge_hint['right_term']}",
                    "<smaller lemma that proves one side of this bridge>",
                ],
                "seed_h_args": seed_h_args,
                "seed_h_args_note": (
                    "Rows were copied from earlier mechanical h-instance search; "
                    "keep or edit the rows that help prove the bridge."
                    if seed_h_args
                    else "No earlier seed rows were available; provide concrete h rows if possible."
                ),
                "why": (
                    "the previous lemma attempt identified this missing bridge; "
                    "try a smaller mechanically provable lemma or add seed_h_args"
                ),
                "requires_llm_content": True,
            })
        module_state = {
            "kind": f"{tool}_tool",
            "tool": tool,
            "target": target,
            "adapter": "tool_call",
            "status": delegated.get("status"),
            "error_code": delegated.get("error_code"),
            "proved_but_unused": proved_unused[:3],
            "candidate_summaries": candidate_summaries[:5],
            "need_hint": {
                "need_hint": (
                    "repair the lemma_hint using the missing bridge, or propose "
                    "a smaller lemma with seed_h_args"
                ),
                "tool": tool,
                "target": target,
                "missing_bridge": bridge_hint or None,
                "proved_but_unused_equations": [
                    item.get("equation")
                    for item in proved_unused[:3]
                    if item.get("equation")
                ],
                "llm_tool_call_templates": llm_templates,
            },
        }
    result = dict(_as_dict(delegated.get("result")) or {
        "status": delegated.get("status"),
        "error_code": delegated.get("error_code"),
        "message": delegated.get("feedback", ""),
    })
    result["module_state"] = module_state
    return {
        "round": round_idx,
        "raw_body": llm_response.get("response", ""),
        "llm_payload": llm_payload,
        "delegated_payload": delegated.get("llm_payload"),
        "tool_call": {
            "tool": tool,
            "target": target,
            "seed_terms": tool_call.get("seed_terms"),
            "budget": tool_call.get("budget"),
            "why": tool_call.get("why"),
        },
        "lemma_hint": delegated.get("lemma_hint"),
        "lemma_chain": delegated.get("lemma_chain"),
        "candidate_summaries": delegated.get("candidate_summaries"),
        "cleaned_body": delegated.get("cleaned_body", ""),
        "lean_code": delegated.get("lean_code", ""),
        "status": delegated.get("status"),
        "error_code": delegated.get("error_code"),
        "feedback": delegated.get("feedback", ""),
        "result": result,
        "search_state": delegated.get("search_state"),
        "lemma_lifecycle": delegated.get("lemma_lifecycle"),
        "module_state": module_state,
    }


def _tool_policy_rejection(
    *,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    previous: list[dict[str, Any]] | None,
    round_idx: int | str,
    llm_response: dict[str, Any],
    llm_payload: dict[str, Any],
    tool: str,
    target: str,
    tool_call: dict[str, Any],
) -> dict[str, Any] | None:
    if not previous or tool not in {"forward_saturation", "saturation", "goal_superposition"}:
        return None
    raw = _as_dict(tool_call.get("raw"))
    if raw.get("override_repeated_tool"):
        return None
    advice = tool_recommendations(problem=problem, h_eq=h_eq, g_eq=g_eq, previous=previous)
    recommended = _as_dict(advice.get("recommended_next_action"))
    if not recommended.get("requires_llm_content"):
        return None
    feedback = (
        "Tool policy rejected this repeated mechanical call because the current "
        "state requires an LLM-filled lemma/midpoint action. Return the "
        "`recommended_next_action` as a concrete `lemma_hint` or `lemma_chain` "
        "tool call, replacing placeholder text with actual equations. If you "
        "intentionally want to retry this mechanical tool, include "
        "`override_repeated_tool: true` and explain the genuinely new parameter."
    )
    module_state = {
        "kind": "tool_call_policy",
        "status": "rejected",
        "tool": tool,
        "target": target,
        "need_hint": {
            "need_hint": "fill the recommended LLM-only lemma/midpoint action",
            "recommended_next_action": recommended,
            "recommendation_note": advice.get("recommendation_note"),
            "llm_only_actions": advice.get("llm_only_actions"),
        },
    }
    return {
        "round": round_idx,
        "raw_body": llm_response.get("response", ""),
        "llm_payload": llm_payload,
        "tool_call": {
            "tool": tool,
            "target": target,
            "seed_terms": tool_call.get("seed_terms"),
            "budget": tool_call.get("budget"),
            "why": tool_call.get("why"),
        },
        "cleaned_body": "",
        "lean_code": "",
        "status": "protocol_rejected",
        "error_code": "NEEDS_LEMMA_TOOL",
        "feedback": feedback + "\n\nRecommended next action:\n" + search_state_text(recommended, max_chars=1800),
        "result": {"status": "protocol_rejected", "error_code": "NEEDS_LEMMA_TOOL", "message": feedback},
        "module_state": module_state,
    }


def tool_call_attempt_from_response(
    *,
    args: argparse.Namespace,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    round_idx: int | str,
    llm_response: dict[str, Any],
    previous: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    tool_call, llm_payload = extract_tool_call(llm_response.get("response", ""))
    if tool_call is None:
        feedback = (
            "Protocol failure: return one JSON object with `kind: tool_call`, "
            "`tool`, `target`, and optional `seed_terms`/`budget`."
        )
        return {
            "round": round_idx,
            "raw_body": llm_response.get("response", ""),
            "llm_payload": llm_payload,
            "cleaned_body": "",
            "lean_code": "",
            "status": "protocol_rejected",
            "error_code": "BAD_TOOL_CALL",
            "feedback": feedback,
            "result": {"status": "protocol_rejected", "message": feedback},
        }

    tool = normalize_tool_name(tool_call["tool"])
    target = tool_call["target"]
    allowed_tools = set(TOOL_REGISTRY)
    if tool not in allowed_tools or target != "goal":
        allowed = [{"tool": name, "target": "goal"} for name in sorted(allowed_tools)]
        allowed.extend([
            {"tool": "lemma_hint", "target": "goal", "lemmas": ["x ◇ y = x ◇ z"]},
            {"tool": "lemma_chain", "target": "goal", "lemmas": ["u ◇ u = v ◇ v"]},
            {
                "tool": "false_model_search",
                "target": "goal",
                "template": "local_search",
                "sizes": [5, 6],
                "seeds": [0, 1, 2],
            },
        ])
        feedback = (
            "Unsupported tool call. This prototype supports the registered "
            "tools with `target: goal`: "
            + ", ".join(f"`{name}`" for name in sorted(allowed_tools))
            + "."
        )
        return {
            "round": round_idx,
            "raw_body": llm_response.get("response", ""),
            "llm_payload": llm_payload,
            "tool_call": tool_call,
            "cleaned_body": "",
            "lean_code": "",
            "status": "protocol_rejected",
            "error_code": "UNSUPPORTED_TOOL_CALL",
            "feedback": feedback,
            "result": {"status": "protocol_rejected", "message": feedback},
            "module_state": {
                "kind": "tool_call_rejected",
                "status": "unsupported",
                "tool_call": tool_call,
                "need_hint": {
                    "need_hint": "call an allowed tool on target goal",
                    "allowed": allowed,
                    "registry": tool_registry_prompt_specs(),
                },
            },
        }

    policy_rejection = _tool_policy_rejection(
        problem=problem,
        h_eq=h_eq,
        g_eq=g_eq,
        previous=previous,
        round_idx=round_idx,
        llm_response=llm_response,
        llm_payload=llm_payload,
        tool=tool,
        target=target,
        tool_call=tool_call,
    )
    if policy_rejection is not None:
        return policy_rejection

    if tool == "lemma_hint":
        delegated = lemma_hint_attempt_from_response(
            args=args,
            problem=problem,
            h_eq=h_eq,
            g_eq=g_eq,
            round_idx=round_idx,
            llm_response=_hint_response_from_tool_call(tool_call, kind="lemma_hint"),
        )
        return _tool_attempt_from_delegated_hint(
            round_idx=round_idx,
            llm_response=llm_response,
            llm_payload=llm_payload,
            tool=tool,
            target=target,
            tool_call=tool_call,
            delegated=delegated,
            previous=previous,
        )

    if tool == "lemma_chain":
        delegated = lemma_chain_attempt_from_response(
            args=args,
            problem=problem,
            h_eq=h_eq,
            g_eq=g_eq,
            round_idx=round_idx,
            llm_response=_hint_response_from_tool_call(tool_call, kind="lemma_chain"),
        )
        return _tool_attempt_from_delegated_hint(
            round_idx=round_idx,
            llm_response=llm_response,
            llm_payload=llm_payload,
            tool=tool,
            target=target,
            tool_call=tool_call,
            delegated=delegated,
            previous=previous,
        )

    if tool == "false_model_search":
        delegated = false_model_hint_attempt_from_response(
            args=args,
            problem=problem,
            h_eq=h_eq,
            g_eq=g_eq,
            round_idx=round_idx,
            llm_response=_false_hint_response_from_tool_call(tool_call),
        )
        return _tool_attempt_from_delegated_false_model(
            round_idx=round_idx,
            llm_response=llm_response,
            llm_payload=llm_payload,
            tool=tool,
            target=target,
            tool_call=tool_call,
            delegated=delegated,
        )

    if tool == "proof_battery":
        result, body, lean_code = run_proof_battery_tool(
            args=args,
            problem=problem,
            h_eq=h_eq,
            g_eq=g_eq,
            tool_call=tool_call,
        )
    elif tool == "grounding_derived":
        result, body, lean_code = run_grounding_derived_tool(
            args=args,
            problem=problem,
            h_eq=h_eq,
            g_eq=g_eq,
            tool_call=tool_call,
        )
    elif tool == "rowconst_certificates":
        result, body, lean_code = run_rowconst_certificates_tool(
            args=args,
            problem=problem,
            h_eq=h_eq,
            g_eq=g_eq,
            tool_call=tool_call,
        )
    elif tool == "right_square_chain":
        result, body, lean_code = run_right_square_chain_tool(
            args=args,
            problem=problem,
            h_eq=h_eq,
            g_eq=g_eq,
            tool_call=tool_call,
        )
    elif tool in {"forward_saturation", "saturation"}:
        result, body, lean_code = run_forward_saturation_tool(
            args=args,
            problem=problem,
            h_eq=h_eq,
            g_eq=g_eq,
            tool_call=tool_call,
        )
    else:
        if tool == "goal_superposition":
            result, body, lean_code = run_goal_superposition_tool(
                args=args,
                problem=problem,
                h_eq=h_eq,
                g_eq=g_eq,
                tool_call={**tool_call, "tool": tool},
            )
        elif tool == "certificates":
            result, body, lean_code = run_certificates_tool(
                args=args,
                problem=problem,
                h_eq=h_eq,
                g_eq=g_eq,
                tool_call={**tool_call, "tool": tool},
            )
        else:
            result, body, lean_code = run_square_sandwich_chain_tool(
                args=args,
                problem=problem,
                h_eq=h_eq,
                g_eq=g_eq,
                tool_call={**tool_call, "tool": tool},
            )
    feedback = feedback_from_result(
        result,
        max_lines=args.max_feedback_lines,
        max_chars=args.max_feedback_chars,
    )
    module_state = _as_dict(result.get("module_state"))
    if module_state and result.get("status") != "accepted":
        feedback += (
            "\n\nTool module state:\n"
            + search_state_text(module_state, max_chars=3500)
        )
    return {
        "round": round_idx,
        "raw_body": llm_response.get("response", ""),
        "llm_payload": llm_payload,
        "tool_call": {
            "tool": tool,
            "target": tool_call.get("target"),
            "seed_terms": tool_call.get("seed_terms"),
            "budget": tool_call.get("budget"),
            "why": tool_call.get("why"),
        },
        "cleaned_body": body,
        "lean_code": lean_code,
        "status": result.get("status"),
        "error_code": result.get("error_code"),
        "feedback": feedback,
        "result": result,
        "module_state": module_state,
    }


def false_model_hint_attempt_from_response(
    *,
    args: argparse.Namespace,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    round_idx: int | str,
    llm_response: dict[str, Any],
) -> dict[str, Any]:
    hints, llm_payload = extract_false_model_hints(llm_response.get("response", ""))
    if not hints:
        feedback = (
            "Protocol failure: return one JSON object with `kind: false_model_hint`, "
            "a `template`, and either `carrier_size`/`sizes` or a full "
            "`counterexample_table`."
        )
        return {
            "round": round_idx,
            "raw_body": llm_response.get("response", ""),
            "llm_payload": llm_payload,
            "cleaned_body": "",
            "lean_code": "",
            "status": "protocol_rejected",
            "error_code": "BAD_FALSE_MODEL_HINT",
            "feedback": feedback,
            "result": {"status": "protocol_rejected", "message": feedback},
        }

    summaries: list[dict[str, Any]] = []
    last_attempt: dict[str, Any] | None = None
    for hint in hints:
        result, lean_code = verify_false_hint(
            args=args,
            problem=problem,
            h_eq=h_eq,
            g_eq=g_eq,
            hint=hint,
        )
        feedback = feedback_from_result(
            result,
            max_lines=args.max_feedback_lines,
            max_chars=args.max_feedback_chars,
        )
        attempt = {
            "round": round_idx,
            "raw_body": llm_response.get("response", ""),
            "llm_payload": llm_payload,
            "false_model_hint": _false_hint_summary(hint),
            "cleaned_body": "",
            "lean_code": lean_code,
            "status": result.get("status"),
            "error_code": result.get("error_code"),
            "feedback": feedback,
            "result": result,
            "module_state": {
                "kind": "false_model_search_state",
                "hint": _false_hint_summary(hint),
                "search_trials": result.get("search_trials") or [],
                "counterexample_size": result.get("counterexample_size"),
                "false_model_source": result.get("false_model_source"),
                "local_check": result.get("local_check"),
                "budget_seconds": result.get("budget_seconds"),
                "search_budget_spent": result.get("search_budget_spent"),
                "budget_remaining": result.get("budget_remaining"),
                "need_hint": result.get("need_hint"),
            },
        }
        summaries.append({
            "hint": _false_hint_summary(hint),
            "status": result.get("status"),
            "error_code": result.get("error_code"),
            "counterexample_size": result.get("counterexample_size"),
            "false_model_source": result.get("false_model_source"),
        })
        attempt["candidate_summaries"] = summaries
        last_attempt = attempt
        if result.get("status") == "accepted":
            return attempt

    assert last_attempt is not None
    last_attempt["feedback"] += (
        "\n\nAll false-model hints failed:\n"
        + search_state_text(summaries, max_chars=2500)
    )
    return last_attempt


def hargs_attempt_from_response(
    *,
    args: argparse.Namespace,
    problem: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    round_idx: int | str,
    llm_response: dict[str, Any],
) -> dict[str, Any]:
    hint_args, llm_payload = extract_h_arg_hints(
        llm_response.get("response", ""),
        len(h_eq["variables"]),
    )
    if not hint_args:
        feedback = (
            "Protocol failure: return exactly one JSON object with `h_args`, "
            "a list of argument lists. Each row must have exactly "
            f"{len(h_eq['variables'])} strings."
        )
        return {
            "round": round_idx,
            "raw_body": llm_response.get("response", ""),
            "llm_payload": llm_payload,
            "cleaned_body": "",
            "lean_code": "",
            "status": "protocol_rejected",
            "error_code": "NO_H_ARG_HINTS",
            "feedback": feedback,
            "result": {"status": "protocol_rejected", "message": feedback},
        }

    graph_body = h_graph_body(
        h_eq,
        g_eq,
        args.max_h_facts,
        extra_args=hint_args,
        congruence_depth=args.congruence_depth,
        max_congruence_facts=args.max_congruence_facts,
    )
    if graph_body is None:
        state = build_search_state(
            h_eq,
            g_eq,
            args.max_h_facts,
            extra_args=hint_args,
            congruence_depth=args.congruence_depth,
            max_congruence_facts=args.max_congruence_facts,
            status="stuck",
            failed_hints=[{
                "kind": "h_args",
                "count": len(hint_args),
                "failure": "graph_no_path",
            }],
        )
        feedback = (
            "No equality path was found from the goal left side to the goal "
            "right side using the generated h-facts plus "
            f"{len(hint_args)} h-arg hints.\n\n"
            "Most useful next hint request:\n"
            f"{search_state_text(state.get('need_hint') or {}, max_chars=1200)}\n\n"
            "Full compact state:\n"
            f"{search_state_text(state)}"
        )
        return {
            "round": round_idx,
            "raw_body": llm_response.get("response", ""),
            "llm_payload": llm_payload,
            "cleaned_body": "",
            "lean_code": "",
            "status": "incorrect",
            "error_code": "H_GRAPH_NO_PATH",
            "feedback": feedback,
            "result": {"status": "incorrect", "message": feedback},
            "search_state": state,
        }

    cleaned = clean_body(graph_body, g_eq["variables"])
    result, lean_code = verify_body(
        problem=problem,
        body=cleaned,
        lean_timeout_seconds=args.lean_timeout_seconds,
        artifact_dir=args.artifact_dir,
    )
    feedback = feedback_from_result(
        result,
        max_lines=args.max_feedback_lines,
        max_chars=args.max_feedback_chars,
    )
    return {
        "round": round_idx,
        "raw_body": llm_response.get("response", ""),
        "llm_payload": llm_payload,
        "cleaned_body": cleaned,
        "lean_code": lean_code,
        "status": result.get("status"),
        "error_code": result.get("error_code"),
        "feedback": feedback,
        "result": result,
    }


def feedback_from_result(result: dict[str, Any], *, max_lines: int, max_chars: int) -> str:
    message = result.get("message") or ""
    if not message:
        message = result.get("stderr") or result.get("stdout") or "(no judge message)"
    lines = message.splitlines()
    kept = "\n".join(lines[:max_lines])
    if len(kept) > max_chars:
        kept = kept[:max_chars] + "\n... (truncated)"
    if "propext" in kept or "DISALLOWED_AXIOMS" in result.get("error_code", ""):
        kept += (
            "\n\nRepair hint: avoid bare `grind` and avoid `simp [e]` / "
            "`simpa [e]` rewrite-list steps. Use explicit equality chaining, "
            "`.trans`, `.symm`, `rw [e]`, or `simpa using named_fact` instead."
        )
    if "unknownIdentifier" in kept or "Unknown identifier" in kept:
        kept += (
            "\n\nRepair hint: do not use variables that have not been introduced "
            "in the goal. Extra arguments to `h` should be existing variables or "
            "compound terms built from them, such as `x`, `y`, `x ◇ y`, or "
            "`(y ◇ (x ◇ y)) ◇ x`."
        )
    return kept


def default_transcript_path(problem_id: str) -> Path:
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    return ROOT / "sidecar_runs" / f"{stamp}_{problem_id}.jsonl"


def append_event(path: Path, event: dict[str, Any]) -> None:
    if event.get("type") == "attempt" and not isinstance(event.get("collaboration_state"), dict):
        event["collaboration_state"] = collaboration_state_from_attempt(event)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(event, ensure_ascii=False) + "\n")


def configure_llm(args: argparse.Namespace) -> dict[str, Any]:
    config = load_config(args.config)
    llm = dict(config["llm"])
    if args.model:
        llm["model"] = args.model
    if args.base_url:
        llm["base_url"] = args.base_url
    if args.api_key_env:
        llm["api_key_env"] = args.api_key_env
    if args.max_output_tokens is not None:
        llm["max_output_tokens"] = args.max_output_tokens
    if args.temperature is not None:
        llm["temperature"] = args.temperature
    if args.http_timeout_seconds is not None:
        llm["http_timeout_seconds"] = args.http_timeout_seconds
    if args.reasoning_effort is not None:
        if args.reasoning_effort:
            llm["reasoning_effort"] = args.reasoning_effort
        else:
            llm.pop("reasoning_effort", None)
    config["llm"] = llm
    return config


def _is_openrouter(base_url: str) -> bool:
    return "openrouter.ai" in base_url.lower()


def _uses_openai_chat_completion_tokens(base_url: str, model: str) -> bool:
    if "api.openai.com" not in base_url.lower():
        return False
    return model.startswith(("gpt-5", "o1", "o3", "o4"))


def call_sidecar_llm(
    prompt: str,
    config: dict[str, Any],
    *,
    max_seconds: float,
    json_response_format: bool,
) -> dict[str, Any]:
    """Call an OpenAI-compatible chat API with a sidecar-friendly envelope.

    The official proxy uses a single user message because contestants provide a
    PROMPT template. For this experiment we want stricter behavior, so use a
    system message and request JSON mode when the provider supports it.
    """
    if not json_response_format:
        return _call_llm(prompt, config, max_seconds=max_seconds)

    llm = config["llm"]
    base_url = (
        llm.get("base_url")
        or os.environ.get("OPENAI_BASE_URL")
        or "https://openrouter.ai/api/v1"
    )
    api_key_env = llm.get("api_key_env")
    if api_key_env:
        api_key = os.environ.get(api_key_env, "")
        if not api_key:
            return {"error": f"{api_key_env} not set"}
    else:
        api_key = os.environ.get("OPENAI_API_KEY") or os.environ.get("OPENROUTER_API_KEY") or ""
        if not api_key:
            return {"error": "OPENAI_API_KEY or OPENROUTER_API_KEY not set"}

    extra_body: dict[str, Any] = {}
    if _is_openrouter(base_url):
        if llm.get("provider"):
            extra_body["provider"] = {"order": [llm["provider"]]}
        if llm.get("reasoning_effort"):
            extra_body["reasoning"] = {"effort": llm["reasoning_effort"]}

    client = OpenAI(api_key=api_key, base_url=base_url, timeout=max(1.0, float(max_seconds)))
    kwargs: dict[str, Any] = {
        "model": llm["model"],
        "messages": [
            {
                "role": "system",
                "content": (
                    "You are a code-only Lean 4 proof generator. Return exactly "
                    "one JSON object. Do not include prose, markdown, analysis, "
                    "or chain-of-thought."
                ),
            },
            {"role": "user", "content": prompt},
        ],
        "temperature": float(llm.get("temperature", 0.0)),
        "response_format": {"type": "json_object"},
    }
    token_key = (
        "max_completion_tokens"
        if _uses_openai_chat_completion_tokens(base_url, llm["model"])
        else "max_tokens"
    )
    kwargs[token_key] = int(llm.get("max_output_tokens", 4096))
    if llm.get("use_seed") and "seed" in llm:
        kwargs["seed"] = llm["seed"]
    if not _is_openrouter(base_url) and llm.get("reasoning_effort"):
        kwargs["reasoning_effort"] = llm["reasoning_effort"]
    if extra_body:
        kwargs["extra_body"] = extra_body

    try:
        try:
            completion = client.chat.completions.create(**kwargs)
        except openai.BadRequestError as exc:
            message = str(exc)
            retried = False
            if "max_tokens" in kwargs and "max_completion_tokens" in message:
                kwargs["max_completion_tokens"] = kwargs.pop("max_tokens")
                retried = True
            if "Unsupported value" in message and "temperature" in message:
                kwargs.pop("temperature", None)
                retried = True
            if "reasoning_effort" in message and "reasoning_effort" in kwargs:
                kwargs.pop("reasoning_effort", None)
                retried = True
            if retried:
                completion = client.chat.completions.create(**kwargs)
            else:
                raise
        choice = completion.choices[0]
        content = getattr(choice.message, "content", None) or ""
        return {"response": content, "finish_reason": getattr(choice, "finish_reason", None)}
    except openai.APIError as exc:
        # Some providers may reject response_format. Fall back to the official
        # proxy path so the experiment remains portable.
        fallback = _call_llm(prompt, config, max_seconds=max_seconds)
        fallback["json_mode_error"] = f"{type(exc).__name__}: {exc}"
        return fallback
    except Exception as exc:  # noqa: BLE001
        return {"error": f"LLM call failed: {type(exc).__name__}: {exc}"}


def run() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--problem-id", help="Problem id to load from official examples")
    parser.add_argument("--problem-file", type=Path, help="JSON/JSONL problem file")
    parser.add_argument(
        "--mode",
        choices=("direct", "lemma", "hargs", "lemma_hint", "lemma_chain", "false_model_hint", "tool_call"),
        default="direct",
    )
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--no-fewshot", action="store_true", help="Omit the built-in accepted proof example")
    parser.add_argument("--no-llm", action="store_true", help="Run only candidate/mechanical pretries; do not call an LLM")
    parser.add_argument(
        "--auto-tool-router",
        action="store_true",
        help="In tool_call mode, choose the next trusted tool with the local recommendation ranker instead of an LLM.",
    )
    parser.add_argument("--dry-run", action="store_true", help="Print first prompt and exit")
    parser.add_argument("--candidate-proof-file", type=Path)
    parser.add_argument("--candidate-json-file", type=Path)
    parser.add_argument("--candidate-proof")
    parser.add_argument("--transcript", type=Path)
    parser.add_argument("--lean-timeout-seconds", type=int, default=120)
    parser.add_argument("--artifact-dir", type=Path, default=OFFICIAL / ".artifacts" / "sidecar")
    parser.add_argument("--max-feedback-lines", type=int, default=45)
    parser.add_argument("--max-feedback-chars", type=int, default=5000)
    parser.add_argument(
        "--max-h-facts",
        type=int,
        default=48,
        help="Number of exact h-instantiation facts to show in the LLM prompt.",
    )
    parser.add_argument(
        "--max-lemma-facts",
        type=int,
        default=96,
        help="Number of lemma instantiations to add when a proved lemma is used on the goal.",
    )
    parser.add_argument(
        "--congruence-depth",
        type=int,
        default=0,
        help="Add this many rounds of congruence-context edges to graph proofs.",
    )
    parser.add_argument(
        "--max-congruence-facts",
        type=int,
        default=240,
        help="Cap generated congruence facts per graph proof.",
    )
    parser.add_argument(
        "--lemma-ce-time-budget",
        type=float,
        default=0.75,
        help="Seconds for small-model refutation of proposed lemmas; 0 disables.",
    )
    parser.add_argument(
        "--lemma-superposition-budget",
        type=float,
        default=0.0,
        help=(
            "Seconds for proof-carrying superposition to prove an LLM lemma "
            "when the h-fact graph cannot."
        ),
    )
    parser.add_argument(
        "--midpoint-superposition-budget",
        type=float,
        default=0.0,
        help=(
            "Seconds for the solver's midpoint stitcher to prove/use an LLM "
            "lemma when graph use does not close the goal."
        ),
    )
    parser.add_argument(
        "--standard-lemma-cert-budget",
        type=float,
        default=0.0,
        help=(
            "If an LLM lemma_hint names an implied standard aux lemma, try this "
            "certificate-consumer budget on the full goal."
        ),
    )
    parser.add_argument(
        "--pretry-superposition-budget",
        type=float,
        default=0.0,
        help="Before LLM calls, try proof-carrying superposition on the goal.",
    )
    parser.add_argument(
        "--preseed-mechanical",
        type=int,
        default=0,
        help="Run this many cheap mechanical proof bodies first and show their feedback to the LLM.",
    )
    parser.add_argument(
        "--pretry-h-graph",
        action="store_true",
        help="Before LLM calls, try a calc proof from the generated exact h-fact graph.",
    )
    parser.add_argument(
        "--false-search-budget",
        type=float,
        default=18.0,
        help="Seconds for each false_model_hint candidate search.",
    )
    parser.add_argument(
        "--false-total-search-budget",
        type=float,
        default=None,
        help=(
            "Total Python countermodel-search seconds shared across all "
            "false_model_hint rounds. This keeps multi-round LLM experiments "
            "at a fixed mechanical budget."
        ),
    )
    parser.add_argument(
        "--false-node-cap",
        type=int,
        default=2_000_000,
        help="Node cap for false_model_hint model_finder searches.",
    )
    parser.add_argument("--config", type=Path, help="Pipeline config for LLM calls")
    parser.add_argument("--model", help="Override config llm.model")
    parser.add_argument("--base-url", help="Override config llm.base_url")
    parser.add_argument("--api-key-env", help="Override config llm.api_key_env")
    parser.add_argument("--max-output-tokens", type=int, default=4096)
    parser.add_argument("--temperature", type=float)
    parser.add_argument("--http-timeout-seconds", type=float, default=120.0)
    parser.add_argument(
        "--no-json-response-format",
        action="store_true",
        help="Do not request provider JSON mode; use the official proxy call shape.",
    )
    parser.add_argument(
        "--reasoning-effort",
        default=None,
        help="Override OpenRouter reasoning effort; pass empty string to omit",
    )
    args = parser.parse_args()

    problem = load_problem(args.problem_id, args.problem_file)
    h_eq, g_eq = parse_problem(problem)
    transcript = args.transcript or default_transcript_path(problem.get("id", "problem"))
    if args.false_total_search_budget is not None:
        setattr(args, "_false_search_budget_remaining", max(0.0, float(args.false_total_search_budget)))

    previous: list[dict[str, Any]] = []
    first_prompt = build_prompt(
        problem=problem,
        h_eq=h_eq,
        g_eq=g_eq,
        mode=args.mode,
        previous=previous,
        include_fewshot=not args.no_fewshot,
        max_h_facts=args.max_h_facts,
    )
    if args.dry_run:
        print(first_prompt)
        print(f"\n# transcript would be: {transcript}")
        return 0

    candidate, candidate_meta = candidate_from_args(args)
    llm_config: dict[str, Any] | None = None if (
        candidate is not None or (args.auto_tool_router and args.mode == "tool_call")
    ) else configure_llm(args)
    initial_tool_recommendations = (
        tool_recommendations(problem=problem, h_eq=h_eq, g_eq=g_eq, previous=previous)
        if args.mode == "tool_call"
        else None
    )

    append_event(transcript, {
        "type": "start",
        "time": time.time(),
        "problem_id": problem.get("id"),
        "mode": args.mode,
        "candidate_meta": candidate_meta,
        "auto_tool_router": bool(args.auto_tool_router),
        "tool_recommendations": initial_tool_recommendations,
        "false_search_budget": args.false_search_budget,
        "false_total_search_budget": args.false_total_search_budget,
    })

    if candidate is None and args.pretry_h_graph:
        graph_body = h_graph_body(
            h_eq,
            g_eq,
            args.max_h_facts,
            congruence_depth=args.congruence_depth,
            max_congruence_facts=args.max_congruence_facts,
        )
        if graph_body:
            cleaned = clean_body(graph_body, g_eq["variables"])
            result, lean_code = verify_body(
                problem=problem,
                body=cleaned,
                lean_timeout_seconds=args.lean_timeout_seconds,
                artifact_dir=args.artifact_dir,
            )
            feedback = feedback_from_result(
                result,
                max_lines=args.max_feedback_lines,
                max_chars=args.max_feedback_chars,
            )
            attempt = {
                "round": "h-graph",
                "source": "h_fact_graph",
                "raw_body": graph_body,
                "llm_payload": {"kind": "mechanical_h_graph"},
                "cleaned_body": cleaned,
                "lean_code": lean_code,
                "status": result.get("status"),
                "error_code": result.get("error_code"),
                "feedback": feedback,
                "result": result,
            }
            previous.append(attempt)
            append_event(transcript, {"type": "attempt", **attempt})
            print(
                f"h-graph: {result.get('status')} "
                f"{result.get('error_code')} transcript={transcript}"
            )
            if result.get("status") == "accepted":
                print("accepted by h-fact graph")
                return 0
        else:
            state = build_search_state(
                h_eq,
                g_eq,
                args.max_h_facts,
                congruence_depth=args.congruence_depth,
                max_congruence_facts=args.max_congruence_facts,
            )
            previous.append({
                "round": "h-graph",
                "raw_body": "",
                "llm_payload": {"kind": "mechanical_h_graph"},
                "cleaned_body": "",
                "lean_code": "",
                "status": "incorrect",
                "error_code": "H_GRAPH_NO_PATH",
                "feedback": "Mechanical h-fact graph found no equality path.",
                "result": {"status": "incorrect", "message": "no path"},
                "search_state": state,
            })
            append_event(transcript, {
                "type": "h_graph",
                "status": "no_path",
                "max_h_facts": args.max_h_facts,
                "search_state": state,
            })
            print(f"h-graph: no_path transcript={transcript}")

    if candidate is None and args.pretry_superposition_budget > 0:
        accepted, attempts = _first_verified_body(
            problem=problem,
            bodies=solver_core.superposition_bodies(
                h_eq,
                g_eq,
                include_aux=True,
                include_goal=True,
                budget=args.pretry_superposition_budget,
            ),
            source="goal_superposition",
            lean_timeout_seconds=args.lean_timeout_seconds,
            artifact_dir=args.artifact_dir,
            max_feedback_lines=args.max_feedback_lines,
            max_feedback_chars=args.max_feedback_chars,
            max_candidates=3,
        )
        module_state = _module_state_from_attempts(
            module="goal_superposition",
            budget=args.pretry_superposition_budget,
            attempts=attempts,
        )
        if accepted is not None:
            attempt = {
                "round": "superposition",
                "llm_payload": {"kind": "mechanical_superposition"},
                **accepted,
                "module_state": module_state,
            }
            previous.append(attempt)
            append_event(transcript, {"type": "attempt", **attempt})
            print(
                f"superposition: {accepted.get('status')} "
                f"{accepted.get('error_code')} transcript={transcript}"
            )
            print("accepted by goal superposition")
            return 0
        previous.append({
            "round": "superposition",
            "raw_body": "",
            "llm_payload": {"kind": "mechanical_superposition"},
            "cleaned_body": "",
            "lean_code": "",
            "status": "incorrect",
            "error_code": "SUPERPOSITION_NO_PROOF",
            "feedback": (
                "Goal superposition did not produce an accepted proof within "
                f"{args.pretry_superposition_budget:.1f}s."
            ),
            "result": {"status": "incorrect", "message": "no accepted superposition body"},
            "module_state": module_state,
        })
        append_event(transcript, {
            "type": "superposition",
            "status": "no_proof",
            "module_state": module_state,
        })
        print(f"superposition: no_proof transcript={transcript}")

    if candidate is None and args.preseed_mechanical:
        seeds = preseed_mechanical_attempts(
            problem=problem,
            h_eq=h_eq,
            g_eq=g_eq,
            count=args.preseed_mechanical,
            lean_timeout_seconds=args.lean_timeout_seconds,
            artifact_dir=args.artifact_dir,
            max_feedback_lines=args.max_feedback_lines,
            max_feedback_chars=args.max_feedback_chars,
        )
        for seed in seeds:
            previous.append(seed)
            append_event(transcript, {"type": "attempt", **seed})
            print(
                f"preseed {seed['round']}: {seed['status']} "
                f"{seed.get('error_code')} transcript={transcript}"
            )
            if seed.get("status") == "accepted":
                print("accepted by mechanical preseed")
                return 0

    if candidate is None and args.no_llm and not (args.auto_tool_router and args.mode == "tool_call"):
        print(f"not accepted by configured mechanical pretries; transcript={transcript}")
        return 1

    for round_idx in range(max(1, args.rounds)):
        prompt = build_prompt(
            problem=problem,
            h_eq=h_eq,
            g_eq=g_eq,
            mode=args.mode,
            previous=previous,
            include_fewshot=not args.no_fewshot,
            max_h_facts=args.max_h_facts,
        )
        append_event(transcript, {
            "type": "prompt",
            "round": round_idx,
            "prompt": prompt,
        })

        if candidate is not None and round_idx == 0:
            raw_body = candidate
            llm_payload = candidate_meta
            llm_response = {"response": raw_body, "source": "candidate"}
        else:
            if args.auto_tool_router and args.mode == "tool_call":
                llm_response = auto_tool_router_response(
                    problem=problem,
                    h_eq=h_eq,
                    g_eq=g_eq,
                    previous=previous,
                )
                append_event(transcript, {
                    "type": "tool_router",
                    "round": round_idx,
                    "response": llm_response,
                })
            else:
                if llm_config is None:
                    llm_config = configure_llm(args)
                t0 = time.time()
                llm_response = call_sidecar_llm(
                    prompt,
                    llm_config,
                    max_seconds=args.http_timeout_seconds,
                    json_response_format=not args.no_json_response_format,
                )
                append_event(transcript, {
                    "type": "llm",
                    "round": round_idx,
                    "elapsed": round(time.time() - t0, 2),
                    "response": llm_response,
                })
            if "error" in llm_response:
                print(f"LLM error: {llm_response['error']}")
                return 2
            if args.mode == "lemma_hint":
                attempt = lemma_hint_attempt_from_response(
                    args=args,
                    problem=problem,
                    h_eq=h_eq,
                    g_eq=g_eq,
                    round_idx=round_idx,
                    llm_response=llm_response,
                )
                previous.append(attempt)
                append_event(transcript, {"type": "attempt", **attempt})
                print(
                    f"round {round_idx}: {attempt.get('status')} "
                    f"{attempt.get('error_code')} transcript={transcript}"
                )
                if attempt.get("status") == "accepted":
                    print("accepted")
                    return 0
                continue
            if args.mode == "lemma_chain":
                attempt = lemma_chain_attempt_from_response(
                    args=args,
                    problem=problem,
                    h_eq=h_eq,
                    g_eq=g_eq,
                    round_idx=round_idx,
                    llm_response=llm_response,
                )
                previous.append(attempt)
                append_event(transcript, {"type": "attempt", **attempt})
                print(
                    f"round {round_idx}: {attempt.get('status')} "
                    f"{attempt.get('error_code')} transcript={transcript}"
                )
                if attempt.get("status") == "accepted":
                    print("accepted")
                    return 0
                continue
            if args.mode == "false_model_hint":
                attempt = false_model_hint_attempt_from_response(
                    args=args,
                    problem=problem,
                    h_eq=h_eq,
                    g_eq=g_eq,
                    round_idx=round_idx,
                    llm_response=llm_response,
                )
                previous.append(attempt)
                append_event(transcript, {"type": "attempt", **attempt})
                print(
                    f"round {round_idx}: {attempt.get('status')} "
                    f"{attempt.get('error_code')} transcript={transcript}"
                )
                if attempt.get("status") == "accepted":
                    print("accepted")
                    return 0
                continue
            if args.mode == "tool_call":
                attempt = tool_call_attempt_from_response(
                    args=args,
                    problem=problem,
                    h_eq=h_eq,
                    g_eq=g_eq,
                    round_idx=round_idx,
                    llm_response=llm_response,
                    previous=previous,
                )
                previous.append(attempt)
                append_event(transcript, {"type": "attempt", **attempt})
                print(
                    f"round {round_idx}: {attempt.get('status')} "
                    f"{attempt.get('error_code')} transcript={transcript}"
                )
                if attempt.get("status") == "accepted":
                    print("accepted")
                    return 0
                continue
            if args.mode == "hargs":
                hint_args, llm_payload = extract_h_arg_hints(
                    llm_response.get("response", ""),
                    len(h_eq["variables"]),
                )
                if not hint_args:
                    feedback = (
                        "Protocol failure: return exactly one JSON object with "
                        "`h_args`, a list of argument lists. Each row must have "
                        f"exactly {len(h_eq['variables'])} strings."
                    )
                    attempt = {
                        "round": round_idx,
                        "raw_body": llm_response.get("response", ""),
                        "llm_payload": llm_payload,
                        "cleaned_body": "",
                        "lean_code": "",
                        "status": "protocol_rejected",
                        "error_code": "NO_H_ARG_HINTS",
                        "feedback": feedback,
                        "result": {"status": "protocol_rejected", "message": feedback},
                    }
                    previous.append(attempt)
                    append_event(transcript, {"type": "attempt", **attempt})
                    print(f"round {round_idx}: protocol_rejected NO_H_ARG_HINTS transcript={transcript}")
                    continue

                graph_body = h_graph_body(
                    h_eq,
                    g_eq,
                    args.max_h_facts,
                    extra_args=hint_args,
                    congruence_depth=args.congruence_depth,
                    max_congruence_facts=args.max_congruence_facts,
                )
                if graph_body is None:
                    state = build_search_state(
                        h_eq,
                        g_eq,
                        args.max_h_facts,
                        extra_args=hint_args,
                        congruence_depth=args.congruence_depth,
                        max_congruence_facts=args.max_congruence_facts,
                    )
                    feedback = (
                        "No equality path was found from the goal left side to "
                        "the goal right side using the generated h-facts plus "
                        f"{len(hint_args)} h-arg hints. Try adding bridge terms "
                        "whose h-instantiation creates the exact middle term "
                        "needed by a `.trans` or `calc` chain.\n\n"
                        "Most useful next hint request:\n"
                        f"{search_state_text(state.get('need_hint') or {}, max_chars=1200)}\n\n"
                        "Full compact state:\n"
                        f"{search_state_text(state)}"
                    )
                    attempt = {
                        "round": round_idx,
                        "raw_body": llm_response.get("response", ""),
                        "llm_payload": llm_payload,
                        "cleaned_body": "",
                        "lean_code": "",
                        "status": "incorrect",
                        "error_code": "H_GRAPH_NO_PATH",
                        "feedback": feedback,
                        "result": {"status": "incorrect", "message": feedback},
                        "search_state": state,
                    }
                    previous.append(attempt)
                    append_event(transcript, {"type": "attempt", **attempt})
                    print(f"round {round_idx}: incorrect H_GRAPH_NO_PATH transcript={transcript}")
                    continue

                cleaned = clean_body(graph_body, g_eq["variables"])
                result, lean_code = verify_body(
                    problem=problem,
                    body=cleaned,
                    lean_timeout_seconds=args.lean_timeout_seconds,
                    artifact_dir=args.artifact_dir,
                )
                feedback = feedback_from_result(
                    result,
                    max_lines=args.max_feedback_lines,
                    max_chars=args.max_feedback_chars,
                )
                attempt = {
                    "round": round_idx,
                    "raw_body": llm_response.get("response", ""),
                    "llm_payload": llm_payload,
                    "cleaned_body": cleaned,
                    "lean_code": lean_code,
                    "status": result.get("status"),
                    "error_code": result.get("error_code"),
                    "feedback": feedback,
                    "result": result,
                }
                previous.append(attempt)
                append_event(transcript, {"type": "attempt", **attempt})
                print(
                    f"round {round_idx}: {result.get('status')} "
                    f"{result.get('error_code')} transcript={transcript}"
                )
                if result.get("status") == "accepted":
                    print("accepted")
                    return 0
                continue
            raw_body, llm_payload = extract_body(llm_response.get("response", ""))

        if candidate is not None and round_idx == 0 and args.mode == "lemma_hint":
            attempt = lemma_hint_attempt_from_response(
                args=args,
                problem=problem,
                h_eq=h_eq,
                g_eq=g_eq,
                round_idx=round_idx,
                llm_response=llm_response,
            )
            previous.append(attempt)
            append_event(transcript, {"type": "attempt", **attempt})
            print(
                f"round {round_idx}: {attempt.get('status')} "
                f"{attempt.get('error_code')} transcript={transcript}"
            )
            if attempt.get("status") == "accepted":
                print("accepted")
                return 0
            break

        if candidate is not None and round_idx == 0 and args.mode == "lemma_chain":
            attempt = lemma_chain_attempt_from_response(
                args=args,
                problem=problem,
                h_eq=h_eq,
                g_eq=g_eq,
                round_idx=round_idx,
                llm_response=llm_response,
            )
            previous.append(attempt)
            append_event(transcript, {"type": "attempt", **attempt})
            print(
                f"round {round_idx}: {attempt.get('status')} "
                f"{attempt.get('error_code')} transcript={transcript}"
            )
            if attempt.get("status") == "accepted":
                print("accepted")
                return 0
            break

        if candidate is not None and round_idx == 0 and args.mode == "false_model_hint":
            attempt = false_model_hint_attempt_from_response(
                args=args,
                problem=problem,
                h_eq=h_eq,
                g_eq=g_eq,
                round_idx=round_idx,
                llm_response=llm_response,
            )
            previous.append(attempt)
            append_event(transcript, {"type": "attempt", **attempt})
            print(
                f"round {round_idx}: {attempt.get('status')} "
                f"{attempt.get('error_code')} transcript={transcript}"
            )
            if attempt.get("status") == "accepted":
                print("accepted")
                return 0
            if args.rounds > 1 and not args.no_llm:
                continue
            break

        if candidate is not None and round_idx == 0 and args.mode == "tool_call":
            attempt = tool_call_attempt_from_response(
                args=args,
                problem=problem,
                h_eq=h_eq,
                g_eq=g_eq,
                round_idx=round_idx,
                llm_response=llm_response,
                previous=previous,
            )
            previous.append(attempt)
            append_event(transcript, {"type": "attempt", **attempt})
            print(
                f"round {round_idx}: {attempt.get('status')} "
                f"{attempt.get('error_code')} transcript={transcript}"
            )
            if attempt.get("status") == "accepted":
                print("accepted")
                return 0
            if args.rounds > 1 and not args.no_llm:
                continue
            break

        if candidate is not None and round_idx == 0 and args.mode == "hargs":
            attempt = hargs_attempt_from_response(
                args=args,
                problem=problem,
                h_eq=h_eq,
                g_eq=g_eq,
                round_idx=round_idx,
                llm_response=llm_response,
            )
            previous.append(attempt)
            append_event(transcript, {"type": "attempt", **attempt})
            print(
                f"round {round_idx}: {attempt.get('status')} "
                f"{attempt.get('error_code')} transcript={transcript}"
            )
            if attempt.get("status") == "accepted":
                print("accepted")
                return 0
            break

        if not raw_body.strip():
            feedback = (
                "Protocol failure: the response did not contain the required JSON "
                "object with a `proof` string, and no Lean code block could be "
                "salvaged. Return exactly one JSON object like "
                "{\"kind\":\"goal_proof\",\"proof\":\"intro x y\\n...\"}."
            )
            attempt = {
                "round": round_idx,
                "raw_body": raw_body,
                "llm_payload": llm_payload,
                "cleaned_body": "",
                "lean_code": "",
                "status": "protocol_rejected",
                "error_code": "NO_JSON_OR_CODE",
                "feedback": feedback,
                "result": {"status": "protocol_rejected", "message": feedback},
            }
            previous.append(attempt)
            append_event(transcript, {"type": "attempt", **attempt})
            print(f"round {round_idx}: protocol_rejected NO_JSON_OR_CODE transcript={transcript}")
            if candidate is not None and round_idx == 0:
                break
            continue

        cleaned = clean_body(raw_body, g_eq["variables"])
        lean_code = solver_core.lean_true(cleaned)
        rejection = local_rejection(cleaned)
        if rejection is not None:
            error_code, feedback = rejection
            result = {
                "status": "locally_rejected",
                "error_code": error_code,
                "message": feedback,
                "verdict": "true",
            }
        else:
            result, lean_code = verify_body(
                problem=problem,
                body=cleaned,
                lean_timeout_seconds=args.lean_timeout_seconds,
                artifact_dir=args.artifact_dir,
            )
            feedback = feedback_from_result(
                result,
                max_lines=args.max_feedback_lines,
                max_chars=args.max_feedback_chars,
            )
        attempt = {
            "round": round_idx,
            "raw_body": raw_body,
            "llm_payload": llm_payload,
            "cleaned_body": cleaned,
            "lean_code": lean_code,
            "status": result.get("status"),
            "error_code": result.get("error_code"),
            "feedback": feedback,
            "result": result,
        }
        previous.append(attempt)
        append_event(transcript, {"type": "attempt", **attempt})

        print(
            f"round {round_idx}: {result.get('status')} "
            f"{result.get('error_code')} transcript={transcript}"
        )
        if result.get("status") == "accepted":
            print("accepted")
            return 0

        # A candidate-only run should not silently switch to the network.
        if candidate is not None and round_idx == 0:
            break

    print(f"not accepted; transcript={transcript}")
    return 1


if __name__ == "__main__":
    raise SystemExit(run())
