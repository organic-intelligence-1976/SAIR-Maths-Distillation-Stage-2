#!/usr/bin/env python3
"""Clean-room probe for residue-controlled symbolic countermodels.

The probe intentionally receives only the two equations. It does not consult
problem IDs, the semantic registry, verified lessons, or cached Lean artifacts.
An LLM selects a bounded family search; the mechanical side searches and tests
operations on Nat of the form

    op(x, y) = max(0, a*x + b*y + c)

with one coefficient triple when x and y have the same residue modulo m and a
second triple otherwise. Passing a finite prefix is discovery evidence, not a
proof. A candidate must later pass the Lean certificate compiler and judge.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from itertools import product
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import baby_solver as solver  # noqa: E402
from scripts.feedback_uptake_probe import call_chat, load_config  # noqa: E402


DEFAULT_ACTION = {
    "kind": "residue_clamped_affine_search",
    "moduli": [2, 3],
    "partition": "same_vs_different",
    "a_values": [-1, 0, 1],
    "b_values": [-1, 0, 1],
    "c_values": [-2, -1, 0, 1, 2],
    "candidate_cap": 2500,
}


def load_problem(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as fh:
        for line in fh:
            if line.strip():
                row = json.loads(line)
                return {
                    "equation1": row["equation1"],
                    "equation2": row["equation2"],
                }
    raise ValueError(f"{path}: no JSONL rows found")


def clamp(value: int) -> int:
    return max(0, value)


def apply_coefficients(coefficients: tuple[int, int, int], x: int, y: int) -> int:
    a, b, c = coefficients
    return clamp(a * x + b * y + c)


def make_operation(
    modulus: int,
    same: tuple[int, int, int],
    different: tuple[int, int, int],
):
    def op(x: int, y: int) -> int:
        coefficients = same if x % modulus == y % modulus else different
        return apply_coefficients(coefficients, x, y)

    return op


def eval_term(term: Any, env: dict[str, int], op) -> int:
    if term[0] == "var":
        return env[term[1]]
    return op(eval_term(term[1], env, op), eval_term(term[2], env, op))


def equation_failures(
    equation: dict[str, Any],
    op,
    *,
    value_limit: int,
    failure_cap: int,
) -> tuple[int, list[dict[str, Any]]]:
    failures = 0
    examples: list[dict[str, Any]] = []
    for values in product(range(value_limit + 1), repeat=len(equation["variables"])):
        env = dict(zip(equation["variables"], values))
        lhs = eval_term(equation["lhs"], env, op)
        rhs = eval_term(equation["rhs"], env, op)
        if lhs == rhs:
            continue
        failures += 1
        if len(examples) < 4:
            examples.append({"env": env, "lhs": lhs, "rhs": rhs})
        if failures >= failure_cap:
            break
    return failures, examples


def goal_witness(
    equation: dict[str, Any],
    op,
    *,
    value_limit: int,
) -> dict[str, Any] | None:
    for values in product(range(value_limit + 1), repeat=len(equation["variables"])):
        env = dict(zip(equation["variables"], values))
        lhs = eval_term(equation["lhs"], env, op)
        rhs = eval_term(equation["rhs"], env, op)
        if lhs != rhs:
            return {"env": env, "lhs": lhs, "rhs": rhs}
    return None


def involution_failures(op, *, value_limit: int, failure_cap: int = 12) -> list[dict[str, int]]:
    failures: list[dict[str, int]] = []
    for a, x in product(range(value_limit + 1), repeat=2):
        result = op(a, op(a, x))
        if result != x:
            failures.append({"a": a, "x": x, "result": result})
            if len(failures) >= failure_cap:
                break
    return failures


def ordered_ints(values: Iterable[Any], *, low: int, high: int) -> list[int]:
    out: list[int] = []
    for value in values:
        try:
            parsed = int(value)
        except (TypeError, ValueError):
            continue
        if low <= parsed <= high and parsed not in out:
            out.append(parsed)
    return out


def normalize_action(action: Any) -> tuple[dict[str, Any] | None, list[str]]:
    repairs: list[str] = []
    if not isinstance(action, dict):
        return None, repairs
    if isinstance(action.get("action"), dict):
        action = action["action"]
        repairs.append("unwrapped_action_envelope")
    kind = str(action.get("kind") or action.get("tool") or "")
    if kind not in {
        "residue_clamped_affine_search",
        "residue_ray_search",
        "symbolic_ray_search",
    }:
        return None, repairs
    moduli = ordered_ints(action.get("moduli") or [action.get("modulus")], low=2, high=5)
    a_values = ordered_ints(action.get("a_values") or [-1, 0, 1], low=-2, high=2)
    b_values = ordered_ints(action.get("b_values") or [-1, 0, 1], low=-2, high=2)
    c_values = ordered_ints(action.get("c_values") or [-2, -1, 0, 1, 2], low=-4, high=4)
    if not moduli or not a_values or not b_values or not c_values:
        return None, repairs
    cap = max(1, min(10_000, int(action.get("candidate_cap") or 2500)))
    return {
        "kind": "residue_clamped_affine_search",
        "moduli": moduli,
        "partition": "same_vs_different",
        "a_values": a_values,
        "b_values": b_values,
        "c_values": c_values,
        "candidate_cap": cap,
    }, repairs


def coefficient_triples(action: dict[str, Any]) -> list[tuple[int, int, int]]:
    triples = list(product(action["a_values"], action["b_values"], action["c_values"]))
    # Translation-like operations are cheap and often make left actions
    # involutive, so inspect them before genuinely two-variable affine rules.
    return sorted(
        triples,
        key=lambda item: (
            item[0] != 0,
            item[1] != 1,
            abs(item[2]),
            abs(item[0]) + abs(item[1] - 1) + abs(item[2]),
            item,
        ),
    )


def search_action(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    action: dict[str, Any],
    *,
    value_limit: int,
    time_budget: float,
) -> dict[str, Any]:
    started = time.monotonic()
    deadline = started + max(0.05, time_budget)
    triples = coefficient_triples(action)
    checked = 0
    best: list[dict[str, Any]] = []
    winner: dict[str, Any] | None = None
    for modulus in action["moduli"]:
        for same, different in product(triples, repeat=2):
            if checked >= action["candidate_cap"] or time.monotonic() >= deadline:
                break
            checked += 1
            op = make_operation(modulus, same, different)
            h_failures, h_examples = equation_failures(
                h_eq,
                op,
                value_limit=value_limit,
                failure_cap=16,
            )
            witness = goal_witness(g_eq, op, value_limit=value_limit)
            involution = involution_failures(op, value_limit=min(value_limit, 8))
            candidate = {
                "modulus": modulus,
                "same": list(same),
                "different": list(different),
                "h_failures": h_failures,
                "h_examples": h_examples,
                "g_witness": witness,
                "involution_failures": involution,
            }
            best.append(candidate)
            best.sort(
                key=lambda row: (
                    row["h_failures"],
                    row["g_witness"] is None,
                    len(row["involution_failures"]),
                    row["modulus"],
                )
            )
            del best[8:]
            if h_failures == 0 and witness is not None:
                winner = candidate
                break
        if winner is not None or checked >= action["candidate_cap"] or time.monotonic() >= deadline:
            break
    return {
        "kind": "ResidueRaySearchState",
        "status": "prefix_candidate_found" if winner else "search_exhausted",
        "action": action,
        "value_limit": value_limit,
        "checked_candidates": checked,
        "elapsed_seconds": round(time.monotonic() - started, 4),
        "winner": winner,
        "best_candidates": best,
        "trust_boundary": (
            "A finite-prefix pass is only a conjecture. The candidate must be "
            "compiled to Lean and accepted by the official judge."
        ),
        "need_hint": (
            None
            if winner
            else "Use the H failures and involution failures to narrow or change the residue family."
        ),
    }


def build_prompt(
    problem: dict[str, Any],
    feedback: list[dict[str, Any]],
    *,
    round_index: int,
) -> str:
    compact_feedback = []
    for state in feedback[-3:]:
        compact_feedback.append({
            "status": state.get("status"),
            "action": state.get("action"),
            "checked_candidates": state.get("checked_candidates"),
            "best_candidates": state.get("best_candidates", [])[:3],
            "need_hint": state.get("need_hint"),
        })
    return "\n".join([
        "You are the untrusted strategy component of an LLM-mechanical magma solver.",
        "You receive only H and G. Do not use benchmark IDs or claim a verdict.",
        "Choose a small symbolic family search. The mechanical side searches parameters,",
        "tests prefixes, reports failures, compiles a proof, and trusts only Lean.",
        f"H must hold universally: {problem['equation1']}",
        f"G must fail somewhere: {problem['equation2']}",
        "",
        "General strategy card:",
        "- If x occurs under two nested left translations in H, consider making",
        "  left translations involutions.",
        "- A small residue class of the left input can select how the right input",
        "  moves. Clamping at zero permits a coherent boundary patch.",
        "- Start with translation-like rules, then widen to two-variable affine rules.",
        "",
        "Available family:",
        "For modulus m and r=(x mod m), s=(y mod m), use",
        "  max(0, a_same*x+b_same*y+c_same) when r=s,",
        "  max(0, a_diff*x+b_diff*y+c_diff) otherwise.",
        "The mechanical side independently chooses one coefficient triple per region",
        "from the value sets you request.",
        "",
        "Return exactly one JSON object of this form:",
        json.dumps(DEFAULT_ACTION, separators=(",", ":")),
        "Keep candidate_cap at most 2500. Prefer the smallest credible coefficient sets.",
        f"This is repair round {round_index}. Mechanical feedback:",
        json.dumps(compact_feedback, ensure_ascii=False, indent=2),
    ])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--problem-file",
        type=Path,
        required=True,
        help="JSONL input; only equation1 and equation2 are read.",
    )
    parser.add_argument(
        "--config",
        type=Path,
        default=ROOT / "configs" / "cerebras_gpt_oss_120b.example.json",
    )
    parser.add_argument("--rounds", type=int, default=2)
    parser.add_argument("--llm-timeout", type=float, default=60.0)
    parser.add_argument("--mechanical-budget", type=float, default=2.0)
    parser.add_argument("--value-limit", type=int, default=12)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / ".artifacts" / "residue_ray_model_probe.json",
    )
    args = parser.parse_args()

    problem = load_problem(args.problem_file)
    h_eq = solver.parse_equation(problem["equation1"])
    g_eq = solver.parse_equation(problem["equation2"])
    config = load_config(args.config)
    started = time.monotonic()
    feedback: list[dict[str, Any]] = []
    rounds: list[dict[str, Any]] = []
    winner: dict[str, Any] | None = None

    for round_index in range(1, max(0, args.rounds) + 1):
        prompt = build_prompt(problem, feedback, round_index=round_index)
        llm = call_chat(prompt, config, timeout=args.llm_timeout)
        parsed = solver.extract_json(llm.get("response", "")) if not llm.get("error") else None
        action, repairs = normalize_action(parsed)
        state = None
        if action is not None:
            state = search_action(
                h_eq,
                g_eq,
                action,
                value_limit=max(2, min(30, args.value_limit)),
                time_budget=args.mechanical_budget,
            )
            feedback.append(state)
            winner = state.get("winner")
        rounds.append({
            "round": round_index,
            "prompt": prompt,
            "llm_error": llm.get("error"),
            "llm_response": llm.get("response"),
            "parsed": parsed,
            "normalized_action": action,
            "schema_repairs": repairs,
            "mechanical_state": state,
        })
        if winner is not None:
            break

    result = {
        "experiment": "id_agnostic_residue_ray_discovery",
        "equation1": problem["equation1"],
        "equation2": problem["equation2"],
        "uses_problem_id": False,
        "uses_semantic_registry": False,
        "uses_verified_lesson": False,
        "uses_cached_certificate": False,
        "winner": winner,
        "rounds": rounds,
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")
    print(json.dumps({
        "output": str(args.output),
        "winner": winner,
        "round_count": len(rounds),
        "elapsed_seconds": result["elapsed_seconds"],
    }, ensure_ascii=False))
    return 0 if winner is not None else 1


if __name__ == "__main__":
    raise SystemExit(main())
