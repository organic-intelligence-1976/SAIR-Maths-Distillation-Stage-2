#!/usr/bin/env python3
"""Sidecar probe for LLM-proposed symbolic false-model families.

This script is intentionally outside the submission solver. It asks an LLM for
compact finite-magma operation families, expands them to tables, and checks the
ordinary false-certificate condition mechanically:

    H holds universally and G fails somewhere.

Promotion rule: only move an idea from this sidecar into `baby_solver.py` after
it produces an accepted countermodel or a verified near miss that improves the
false-search feedback loop.
"""

from __future__ import annotations

import argparse
import ast
import json
import sys
import time
from collections import Counter
from itertools import product
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import baby_solver as solver  # noqa: E402
from scripts.feedback_uptake_probe import call_chat, load_config, load_first_problem  # noqa: E402


BIN_OPS = {
    ast.Add: lambda a, b: a + b,
    ast.Sub: lambda a, b: a - b,
    ast.Mult: lambda a, b: a * b,
    ast.FloorDiv: lambda a, b: a // b if b else 0,
    ast.Mod: lambda a, b: a % b if b else 0,
}
CMP_OPS = {
    ast.Eq: lambda a, b: a == b,
    ast.NotEq: lambda a, b: a != b,
    ast.Lt: lambda a, b: a < b,
    ast.LtE: lambda a, b: a <= b,
    ast.Gt: lambda a, b: a > b,
    ast.GtE: lambda a, b: a >= b,
}


def safe_eval_expr(text: str, env: dict[str, int]) -> int | bool:
    """Evaluate a small arithmetic/boolean expression over i, j, n."""
    text = text.replace("&&", " and ").replace("||", " or ")

    def walk(node: ast.AST) -> int | bool:
        if isinstance(node, ast.Expression):
            return walk(node.body)
        if isinstance(node, ast.Constant) and isinstance(node.value, (int, bool)):
            return node.value
        if isinstance(node, ast.Name) and node.id in env:
            return env[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -int(walk(node.operand))
        if isinstance(node, ast.BinOp) and type(node.op) in BIN_OPS:
            return BIN_OPS[type(node.op)](int(walk(node.left)), int(walk(node.right)))
        if isinstance(node, ast.BoolOp):
            vals = [bool(walk(value)) for value in node.values]
            if isinstance(node.op, ast.And):
                return all(vals)
            if isinstance(node.op, ast.Or):
                return any(vals)
        if isinstance(node, ast.Compare):
            left = walk(node.left)
            for op, right_node in zip(node.ops, node.comparators):
                right = walk(right_node)
                if type(op) not in CMP_OPS or not CMP_OPS[type(op)](int(left), int(right)):
                    return False
                left = right
            return True
        raise ValueError(f"unsupported expression: {ast.dump(node)}")

    parsed = ast.parse(text, mode="eval")
    return walk(parsed)


def default_value(default: Any, i: int, j: int, n: int) -> int:
    if isinstance(default, str):
        kind = default.lower()
        params: list[int] = []
    elif isinstance(default, dict):
        kind = str(default.get("kind") or default.get("name") or "right").lower()
        params = [int(x) for x in default.get("params") or []]
    else:
        kind = "right"
        params = []
    if kind in {"right", "proj_r", "second"}:
        return j % n
    if kind in {"left", "proj_l", "first"}:
        return i % n
    if kind == "constant":
        return (params[0] if params else 0) % n
    if kind == "affine":
        a, b, c = (params + [0, 1, 0])[:3]
        return (a * i + b * j + c) % n
    if kind == "bilinear":
        a, b, c, d = (params + [0, 1, 0, 0])[:4]
        return (a * i + b * j + c * i * j + d) % n
    if kind == "quadratic":
        a, b, c, d, e, f = (params + [0, 1, 0, 0, 0, 0])[:6]
        return (a * i + b * j + c * i * j + d * i * i + e * j * j + f) % n
    return j % n


def rule_applies(rule: dict[str, Any], i: int, j: int, n: int) -> bool:
    when = rule.get("when") or rule.get("if") or rule.get("condition")
    if when is None:
        return False
    if isinstance(when, str):
        return bool(safe_eval_expr(when, {"i": i, "j": j, "n": n}))
    if isinstance(when, dict):
        kind = str(when.get("kind") or "").lower()
        if kind in {"diagonal", "diag"}:
            return i == j
        if kind in {"off_diagonal", "offdiag"}:
            return i != j
        if kind in {"same_mod", "same_residue"}:
            mod = max(1, int(when.get("mod") or 2))
            return (i - j) % mod == 0
        if kind in {"cell", "patch"}:
            return i == int(when.get("i")) and j == int(when.get("j"))
    return False


def rule_value(rule: dict[str, Any], i: int, j: int, n: int) -> int:
    value = rule.get("value", rule.get("then", j))
    if isinstance(value, int):
        return value % n
    if isinstance(value, str):
        return int(safe_eval_expr(value, {"i": i, "j": j, "n": n})) % n
    if isinstance(value, dict):
        return default_value(value, i, j, n)
    return j % n


def table_from_candidate(candidate: dict[str, Any]) -> tuple[list[list[int]], dict[str, Any]]:
    n = int(candidate.get("carrier_size") or candidate.get("n") or 0)
    if n < 2 or n > 40:
        raise ValueError(f"carrier_size must be in 2..40, got {n}")
    default = candidate.get("default") or candidate.get("operation") or {"kind": "right"}
    rules = candidate.get("rules") or []
    patches = candidate.get("patches") or []
    table: list[list[int]] = []
    touched: Counter[tuple[int, int]] = Counter()
    for i in range(n):
        row: list[int] = []
        for j in range(n):
            value = default_value(default, i, j, n)
            for rule in rules:
                if isinstance(rule, dict) and rule_applies(rule, i, j, n):
                    value = rule_value(rule, i, j, n)
                    touched[(i, j)] += 1
            row.append(value % n)
        table.append(row)
    for patch in patches:
        if isinstance(patch, (list, tuple)) and len(patch) == 3:
            i, j, value = (int(patch[0]), int(patch[1]), int(patch[2]))
        elif isinstance(patch, dict):
            i, j, value = int(patch["i"]), int(patch["j"]), int(patch["value"])
        else:
            continue
        if 0 <= i < n and 0 <= j < n:
            table[i][j] = value % n
            touched[(i, j)] += 1
    return table, {
        "n": n,
        "rule_count": len(rules),
        "patch_count": len(patches),
        "touched_cells": len(touched),
    }


def eval_with_cells(term: Any, env: dict[str, int], table: list[list[int]], cells: Counter[tuple[int, int]]) -> int:
    if term[0] == "var":
        return env[term[1]]
    left = eval_with_cells(term[1], env, table, cells)
    right = eval_with_cells(term[2], env, table, cells)
    cells[(left, right)] += 1
    return table[left][right]


def check_candidate(h_eq: dict[str, Any], g_eq: dict[str, Any], candidate: dict[str, Any]) -> dict[str, Any]:
    try:
        table, table_meta = table_from_candidate(candidate)
    except Exception as exc:
        return {"ok": False, "error": str(exc), "candidate": candidate}
    n = len(table)
    h_violations = 0
    g_failures = 0
    examples_h: list[dict[str, Any]] = []
    examples_g: list[dict[str, Any]] = []
    hot_h: Counter[tuple[int, int]] = Counter()
    hot_g: Counter[tuple[int, int]] = Counter()

    for vals in product(range(n), repeat=len(h_eq["variables"])):
        env = dict(zip(h_eq["variables"], vals))
        cells: Counter[tuple[int, int]] = Counter()
        lhs = eval_with_cells(h_eq["lhs"], env, table, cells)
        rhs = eval_with_cells(h_eq["rhs"], env, table, cells)
        if lhs != rhs:
            h_violations += 1
            hot_h.update(cells)
            if len(examples_h) < 5:
                examples_h.append({"env": env, "lhs": lhs, "rhs": rhs, "cells": [list(c) for c in cells]})

    for vals in product(range(n), repeat=len(g_eq["variables"])):
        env = dict(zip(g_eq["variables"], vals))
        cells = Counter()
        lhs = eval_with_cells(g_eq["lhs"], env, table, cells)
        rhs = eval_with_cells(g_eq["rhs"], env, table, cells)
        if lhs != rhs:
            g_failures += 1
            hot_g.update(cells)
            if len(examples_g) < 5:
                examples_g.append({"env": env, "lhs": lhs, "rhs": rhs, "cells": [list(c) for c in cells]})

    return {
        "ok": True,
        "is_counterexample": h_violations == 0 and g_failures > 0,
        "h_violations": h_violations,
        "g_failures": g_failures,
        "table_meta": table_meta,
        "candidate_summary": {
            "carrier_size": n,
            "default": candidate.get("default"),
            "rules": candidate.get("rules"),
            "patch_count": len(candidate.get("patches") or []),
            "why": candidate.get("why"),
        },
        "h_examples": examples_h,
        "g_examples": examples_g,
        "hot_h_cells": [{"cell": list(k), "count": v} for k, v in hot_h.most_common(10)],
        "hot_g_cells": [{"cell": list(k), "count": v} for k, v in hot_g.most_common(10)],
        "table": table if n <= 12 else None,
    }


def built_in_candidates() -> list[dict[str, Any]]:
    candidates: list[dict[str, Any]] = []
    for n in (8, 12, 20):
        candidates.extend([
            {"carrier_size": n, "default": {"kind": "right"}, "rules": [], "why": "right projection baseline"},
            {"carrier_size": n, "default": {"kind": "left"}, "rules": [], "why": "left projection baseline"},
            {"carrier_size": n, "default": {"kind": "affine", "params": [0, 1, 0]}, "rules": [
                {"when": "i == j", "value": "i + 1"}
            ], "why": "right projection with shifted diagonal"},
            {"carrier_size": n, "default": {"kind": "affine", "params": [0, 1, 0]}, "rules": [
                {"when": "i % 2 == j % 2", "value": "i"},
                {"when": "i % 2 != j % 2", "value": "j"},
            ], "why": "two-region parity operation"},
            {"carrier_size": n, "default": {"kind": "affine", "params": [1, 1, 0]}, "rules": [
                {"when": "i == j", "value": "j"}
            ], "why": "addition with projection diagonal"},
        ])
    return candidates


def build_prompt(problem: dict[str, Any], feedback: list[dict[str, Any]], max_candidates: int) -> str:
    compact = [
        {
            "carrier_size": row.get("candidate_summary", {}).get("carrier_size"),
            "default": row.get("candidate_summary", {}).get("default"),
            "rules": row.get("candidate_summary", {}).get("rules"),
            "h_violations": row.get("h_violations"),
            "g_failures": row.get("g_failures"),
            "hot_h_cells": row.get("hot_h_cells", [])[:4],
            "hot_g_cells": row.get("hot_g_cells", [])[:4],
            "h_examples": row.get("h_examples", [])[:2],
            "g_examples": row.get("g_examples", [])[:2],
        }
        for row in feedback[:8]
    ]
    return "\n".join([
        "Return exactly one JSON object. You are proposing compact finite-magma counterexample families.",
        "The trusted mechanical checker will expand and verify your candidates; do not claim success unless checked.",
        f"Problem id: {problem.get('id')}",
        f"H must hold universally: {problem.get('equation1')}",
        f"G must fail for at least one assignment: {problem.get('equation2')}",
        "Candidate DSL:",
        json.dumps({
            "kind": "false_model_family_candidates",
            "candidates": [{
                "carrier_size": 20,
                "default": {"kind": "right | left | constant | affine | bilinear | quadratic", "params": [0, 1, 0]},
                "rules": [
                    {"when": "i == j", "value": "i + 1"},
                    {"when": "i % 2 == j % 2", "value": "i"}
                ],
                "patches": [[0, 1, 5]],
                "why": "short reason"
            }]
        }, indent=2),
        "Use structured families: parity/residue classes, diagonal/off-diagonal laws, affine regions, or compact piecewise rules.",
        "Avoid arbitrary sparse patches unless they are consequences of a family.",
        "Exploration rule: return candidates even if you are unsure. A near miss with fewer H violations or more G failures is useful feedback.",
        "Projection defaults that satisfy H exactly but have zero G failures are sterile; perturb them with a coherent family law.",
        "Mechanical feedback from checked candidates:",
        json.dumps(compact, indent=2, ensure_ascii=False),
        f"Return between 3 and {max_candidates} candidates.",
    ])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--problem-file", type=Path, default=ROOT / ".artifacts" / "hard2_0027_only.jsonl")
    parser.add_argument("--config", type=Path, default=ROOT / ".artifacts" / "openrouter_fast_config.json")
    parser.add_argument("--output", type=Path, default=ROOT / ".artifacts" / "symbolic_ce_family_probe.json")
    parser.add_argument("--llm-rounds", type=int, default=1)
    parser.add_argument("--max-candidates", type=int, default=6)
    parser.add_argument("--timeout", type=float, default=90.0)
    args = parser.parse_args()

    problem = load_first_problem(args.problem_file)
    h_eq = solver.parse_equation(problem["equation1"])
    g_eq = solver.parse_equation(problem["equation2"])
    started = time.monotonic()

    checked: list[dict[str, Any]] = [check_candidate(h_eq, g_eq, cand) for cand in built_in_candidates()]
    llm_rounds: list[dict[str, Any]] = []
    config = load_config(args.config)

    for round_idx in range(max(0, args.llm_rounds)):
        prompt = build_prompt(problem, sorted(
            checked,
            key=lambda row: (row.get("h_violations", 10**9), -row.get("g_failures", 0)),
        ), args.max_candidates)
        llm = call_chat(prompt, config, timeout=args.timeout)
        parsed = solver.extract_json(llm.get("response", "")) if not llm.get("error") else None
        candidates = []
        if isinstance(parsed, dict):
            raw = parsed.get("candidates") or parsed.get("families") or []
            if isinstance(raw, list):
                candidates = [x for x in raw if isinstance(x, dict)][: args.max_candidates]
        results = [check_candidate(h_eq, g_eq, cand) for cand in candidates]
        checked.extend(results)
        llm_rounds.append({
            "round": round_idx + 1,
            "prompt_chars": len(prompt),
            "llm_error": llm.get("error"),
            "response": llm.get("response"),
            "parsed": parsed,
            "candidate_count": len(candidates),
            "results": results,
        })
        if any(row.get("is_counterexample") for row in results):
            break

    best = sorted(
        [row for row in checked if row.get("ok")],
        key=lambda row: (row.get("h_violations", 10**9), -row.get("g_failures", 0)),
    )[:10]
    output = {
        "problem_id": problem.get("id"),
        "equation1": problem.get("equation1"),
        "equation2": problem.get("equation2"),
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "found_counterexample": any(row.get("is_counterexample") for row in checked),
        "best_checked": best,
        "llm_rounds": llm_rounds,
        "checked_count": len(checked),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2, ensure_ascii=False), encoding="utf-8")
    print(json.dumps({
        "output": str(args.output),
        "found_counterexample": output["found_counterexample"],
        "checked_count": output["checked_count"],
        "best": [
            {
                "h_violations": row.get("h_violations"),
                "g_failures": row.get("g_failures"),
                "summary": row.get("candidate_summary"),
            }
            for row in best[:3]
        ],
    }, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
