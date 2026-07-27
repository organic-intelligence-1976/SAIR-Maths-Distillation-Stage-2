#!/usr/bin/env python3
"""Compare Stage-1-prior routing with and without mechanical feedback.

This is a research probe, not submission code.  It creates the same cheap
true/false scout state for every problem, asks the same LLM for one bounded
next action, and varies only whether the prompt includes those scout states.
The hidden answer is used solely for scoring after the response.
"""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import UTC, datetime
import json
from pathlib import Path
import sys
import time
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import baby_solver as solver  # noqa: E402
from research_system.executor import MechanicalExecutor  # noqa: E402
from research_system.protocol import ProblemSpec  # noqa: E402
from research_system.verifier import OfficialLeanVerifier  # noqa: E402
from scripts.feedback_uptake_probe import call_chat, load_config  # noqa: E402


DEFAULT_CASES = ROOT / "data" / "routing_probe_cases.jsonl"
DEFAULT_CONFIG = ROOT / "configs" / "cerebras_gpt_oss_120b.example.json"
DEFAULT_OUTPUT = ROOT / ".artifacts" / "stage1_routing_probe.json"
MODES = ("stage1_only", "stage1_feedback", "stage1_feedback_calibrated")
TRUE_TOOLS = {
    name for name, spec in solver.TOOL_REGISTRY.items() if spec.get("domain") == "true"
}
FALSE_TOOLS = {
    name for name, spec in solver.TOOL_REGISTRY.items() if spec.get("domain") == "false"
}


def read_jsonl(path: Path) -> list[ProblemSpec]:
    rows: list[ProblemSpec] = []
    with path.open("r", encoding="utf-8") as fh:
        for line in fh:
            if line.strip():
                rows.append(ProblemSpec.from_mapping(json.loads(line)))
    return rows


def op_count(term: Any) -> int:
    if term[0] != "op":
        return 0
    return 1 + op_count(term[1]) + op_count(term[2])


def variable_counts(term: Any) -> Counter[str]:
    if term[0] == "var":
        return Counter([str(term[1])])
    return variable_counts(term[1]) + variable_counts(term[2])


def is_square(term: Any) -> bool:
    return term[0] == "op" and term[1] == term[2] and term[1][0] == "var"


def stage1_features(h_eq: dict[str, Any], g_eq: dict[str, Any]) -> dict[str, Any]:
    counts = variable_counts(h_eq["lhs"]) + variable_counts(h_eq["rhs"])
    m = min(counts.values()) if counts else 0
    s = op_count(h_eq["lhs"])
    v = len(variable_counts(h_eq["lhs"]))
    c1 = op_count(h_eq["lhs"]) + op_count(h_eq["rhs"])
    c2 = op_count(g_eq["lhs"]) + op_count(g_eq["rhs"])
    if c2 > c1 + 2 and m == 1:
        rule, prediction = "B0", "false"
    elif m >= 2:
        rule, prediction = "B1", "false"
    elif s == 0:
        rule, prediction = "B2a", "true"
    elif s == 1 and v == 2:
        rule, prediction = "B2b", "true"
    elif s == 1 and v == 1 and is_square(h_eq["lhs"]) and is_square(g_eq["lhs"]):
        rule, prediction = "B2c", "true"
    else:
        rule, prediction = "B2d", "false"
    return {
        "M": m,
        "S": s,
        "V": v,
        "C1": c1,
        "C2": c2,
        "rule": rule,
        "prediction": prediction,
        "variable_counts": dict(sorted(counts.items())),
    }


def compact_state(state: dict[str, Any], keys: tuple[str, ...]) -> dict[str, Any]:
    return {key: state.get(key) for key in keys if state.get(key) is not None}


def cheap_scouts(problem: ProblemSpec) -> dict[str, Any]:
    h_eq = solver.parse_equation(problem.equation1)
    g_eq = solver.parse_equation(problem.equation2)
    started = time.monotonic()
    body, battery_state = solver.proof_battery_graph_body(h_eq, g_eq, max_layers=2)
    graph_state = solver.graph_search_state(
        h_eq,
        g_eq,
        h_limit=36,
        lemma_limit=80,
        congruence_cap=400,
    )
    found, false_state = solver.false_model_search_detailed(
        h_eq,
        g_eq,
        {
            "kind": "tool_call",
            "tool": "false_model_search",
            "routes": ["model_finder_v2:n=4", "skew_product:2x2"],
            "budget": 4,
        },
        4,
    )
    return {
        "seconds": round(time.monotonic() - started, 4),
        "true_candidate": body,
        "false_candidate": found,
        "true_state": {
            "proof_battery": compact_state(
                battery_state,
                ("kind", "status", "graph_layers_considered", "need_hint"),
            ),
            "graph": compact_state(
                graph_state,
                (
                    "kind",
                    "status",
                    "facts_generated",
                    "left_component_size",
                    "right_component_size",
                    "components_connected",
                    "closest_pairs",
                    "recommended_next_action",
                    "need_hint",
                ),
            ),
        },
        "false_state": compact_state(
            false_state,
            (
                "kind",
                "status",
                "budget_seconds",
                "trials",
                "diagnostic_highlights",
                "untried_requested_routes",
                "recommended_next_call",
                "need_hint",
            ),
        ),
    }


def prior_text(features: dict[str, Any]) -> str:
    return "\n".join(
        [
            "Stage-1 strict TRUE checks (use only when the syntax matches exactly):",
            "A1 same sides; A2 one consistent variable renaming of H; A3 a bare "
            "H variable absent from the opposite side; A4/A5 literal left/right "
            "projection pins; A6/A7 literal unary pins; A8 literal product "
            "collapse; A9 exact subterm rewriting without rebracketing.",
            "Stage-1 fallback prior (calibrated verdict prior, never a proof):",
            "B0: C2 > C1+2 and M=1 -> false.",
            "B1: M>=2 -> false.",
            "B2a: M=1 and H lhs is a variable -> true.",
            "B2b: M=1 and H lhs is one product of two variables -> true.",
            "B2c: M=1 and both left sides are variable squares -> true.",
            "Otherwise B2d -> false.",
            "M is minimum H-variable occurrence count; S is H-lhs op count; "
            "V is H-lhs distinct-variable count; C1/C2 are total H/G op counts.",
            "Computed features: " + json.dumps(features, sort_keys=True),
        ]
    )


def build_prompt(
    problem: ProblemSpec,
    mode: str,
    features: dict[str, Any],
    invariant_report: list[dict[str, Any]],
    scouts: dict[str, Any],
    action_budget: float,
) -> str:
    lines = [
        "You route one next attempt in a trusted LLM-mechanical magma solver.",
        "Do not issue a verdict. Choose the wing and one concrete bounded action.",
        "The action is an untrusted suggestion and will be normalized, executed, "
        "and Lean-verified mechanically.",
        f"Problem: {problem.id}",
        f"H: {problem.equation1}",
        f"G: {problem.equation2}",
        prior_text(features),
        "Strict invariant checks already computed:",
        json.dumps(invariant_report, ensure_ascii=False, sort_keys=True),
    ]
    if mode != "stage1_only":
        lines.extend(
            [
                "Actual cheap-scout feedback:",
                json.dumps(
                    {
                        "true_attempt": scouts["true_state"],
                        "false_attempt": scouts["false_state"],
                    },
                    ensure_ascii=False,
                    sort_keys=True,
                ),
                "A mechanical recommendation is only a local continuation, not "
                "evidence that its wing is globally correct. Override it when the "
                "other wing is better supported.",
            ]
        )
        if mode == "stage1_feedback_calibrated":
            lines.extend(
                [
                    "Evidence calibration for this experiment:",
                    "- recommended_next_call is emitted by a fixed continuation "
                    "policy after every miss. Its presence is not case-specific "
                    "and must not influence the wing choice.",
                    "- no model at carrier 4 and infeasibility of one 2x2 symbolic "
                    "family are weak TRUE evidence, not proof.",
                    "- disconnected true components are weak FALSE evidence, not proof.",
                    "- a proposed bridge identical to the entire goal is invalid "
                    "because it does not split the proof.",
                    "- use case-specific frontier sizes, trial effort, equation "
                    "structure, and the Stage-1 prior. Do not merely copy either "
                    "scout's suggested action.",
                ]
            )
    else:
        lines.append(
            "No attempt feedback is available in this arm. Route from the problem, "
            "strict checks, and the calibrated prior."
        )
    lines.extend(
        [
            f"One action receives at most {action_budget:g} seconds.",
            "Allowed true actions include:",
            '{"kind":"tool_call","tool":"proof_battery","target":"goal","max_graph_candidates":4}',
            '{"kind":"tool_call","tool":"forward_saturation","target":"goal","budget":8}',
            '{"kind":"tool_call","tool":"goal_superposition","target":"goal","budget":8}',
            '{"kind":"tool_call","tool":"standard_aux_superposition","target":"goal","lemmas":["const","proj_l","proj_r","rowconst"],"budget":10}',
            '{"kind":"tool_call","tool":"helper_chain_portfolio","target":"goal","budget":12}',
            '{"kind":"midpoint","lemma":"<a concrete universal equation>","why":"<bridge rationale>"}',
            "Allowed false actions include exactly one bounded route:",
            '{"kind":"tool_call","tool":"false_model_search","target":"goal","routes":["skew_product:2x3"],"budget":8}',
            '{"kind":"tool_call","tool":"false_model_search","target":"goal","routes":["local_search:n=6:seed=2"],"budget":8}',
            '{"kind":"tool_call","tool":"false_model_search","target":"goal","routes":["cp_sat:n=6"],"budget":8}',
            '{"kind":"tool_call","tool":"false_model_search","target":"goal","routes":["poly_ce:tier=2:nmax=13"],"budget":8}',
            '{"kind":"tool_call","tool":"false_model_search","target":"goal","routes":["structured_ce:max_n=7"],"budget":8}',
            "Return exactly:",
            '{"kind":"schedule_next","wing":"true|false","confidence":0.0,'
            '"action":{...},"reason_codes":["short_code"],'
            '"switch_if":"observable condition for changing wings"}',
            "Use no placeholder inside action. Keep reason_codes concise.",
        ]
    )
    return "\n".join(lines)


def action_wing(action: dict[str, Any] | None) -> str | None:
    if not action:
        return None
    if action.get("verdict") == "false" or action.get("kind") in {
        "false_table",
        "false_model_family",
        "infinite_model",
    }:
        return "false"
    if action.get("verdict") == "true" or action.get("kind") == "goal_proof":
        return "true"
    tool = solver.TOOL_ALIASES.get(str(action.get("tool") or ""), action.get("tool"))
    if tool in TRUE_TOOLS:
        return "true"
    if tool in FALSE_TOOLS:
        return "false"
    if solver.is_hint_payload(action):
        return "true"
    return None


def clamp_action(action: dict[str, Any], max_budget: float) -> dict[str, Any]:
    out = dict(action)
    if "budget" in out or out.get("kind") == "tool_call":
        try:
            out["budget"] = min(max_budget, max(0.5, float(out.get("budget") or max_budget)))
        except (TypeError, ValueError):
            out["budget"] = max_budget
    if out.get("tool") == "false_model_search":
        routes = [str(route) for route in out.get("routes") or []]
        out["routes"] = routes[:1]
        out["max_routes"] = 1
    return out


def run_arm(
    problem: ProblemSpec,
    mode: str,
    config: dict[str, Any],
    scouts: dict[str, Any],
    action_budget: float,
    llm_timeout: float,
    verify: bool,
) -> dict[str, Any]:
    h_eq = solver.parse_equation(problem.equation1)
    g_eq = solver.parse_equation(problem.equation2)
    features = stage1_features(h_eq, g_eq)
    invariant_report = solver.symbolic_invariant_report(h_eq, g_eq)
    prompt = build_prompt(
        problem,
        mode,
        features,
        invariant_report,
        scouts,
        action_budget,
    )
    started = time.monotonic()
    llm = call_chat(prompt, config, llm_timeout)
    parsed = solver.extract_json(llm.get("response", "")) if not llm.get("error") else None
    declared_wing = str(parsed.get("wing") or "").lower() if parsed else None
    raw_action = parsed.get("action") if parsed and isinstance(parsed.get("action"), dict) else None
    bounded_action = clamp_action(raw_action, action_budget) if raw_action else None
    normalized, adapter_state = (
        MechanicalExecutor.normalize(bounded_action) if bounded_action else (None, None)
    )
    actual_wing = action_wing(normalized)
    wing_consistent = bool(
        declared_wing in {"true", "false"} and actual_wing == declared_wing
    )
    execution = None
    verification = None
    if normalized is not None and wing_consistent:
        execution = MechanicalExecutor().execute(
            problem,
            normalized,
            action_is_normalized=True,
            adapter_state=adapter_state,
        )
        if verify and execution.has_candidate:
            verification = OfficialLeanVerifier(timeout_seconds=45).verify(problem, execution)
    answer_wing = "true" if problem.answer else "false"
    return {
        "mode": mode,
        "case_id": problem.id,
        "answer_wing": answer_wing,
        "features": features,
        "prompt": prompt,
        "llm_error": llm.get("error"),
        "llm_response": llm.get("response"),
        "parsed": parsed,
        "declared_wing": declared_wing,
        "actual_action_wing": actual_wing,
        "wing_consistent": wing_consistent,
        "wing_correct": declared_wing == answer_wing,
        "bounded_action": bounded_action,
        "normalized_action": normalized,
        "adapter_state": adapter_state,
        "execution": execution.to_mapping(include_code=True) if execution else None,
        "verification": verification.to_mapping() if verification else None,
        "accepted": bool(verification and verification.accepted),
        "seconds": round(time.monotonic() - started, 4),
    }


def summarize(cases: list[dict[str, Any]], arms: list[dict[str, Any]]) -> dict[str, Any]:
    by_mode: dict[str, Any] = {}
    for mode in MODES:
        rows = [row for row in arms if row["mode"] == mode]
        by_mode[mode] = {
            "cases": len(rows),
            "parse_successes": sum(row["parsed"] is not None for row in rows),
            "wing_consistent_actions": sum(row["wing_consistent"] for row in rows),
            "wing_correct": sum(row["wing_correct"] for row in rows),
            "candidate_ready": sum(
                bool((row.get("execution") or {}).get("body"))
                or (row.get("execution") or {}).get("finite_table") is not None
                or bool((row.get("execution") or {}).get("infinite_code"))
                for row in rows
            ),
            "judge_accepted": sum(row["accepted"] for row in rows),
            "true_cases_correct": sum(
                row["wing_correct"] and row["answer_wing"] == "true" for row in rows
            ),
            "false_cases_correct": sum(
                row["wing_correct"] and row["answer_wing"] == "false" for row in rows
            ),
        }
    deterministic_correct = sum(
        row["stage1_prediction"] == row["answer_wing"] for row in cases
    )
    true_first_correct = sum(row["answer_wing"] == "true" for row in cases)
    return {
        "case_count": len(cases),
        "baselines": {
            "fixed_true_first_wing_correct": true_first_correct,
            "deterministic_stage1_wing_correct": deterministic_correct,
        },
        "modes": by_mode,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cases", type=Path, default=DEFAULT_CASES)
    parser.add_argument("--config", type=Path, default=DEFAULT_CONFIG)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--action-budget", type=float, default=12.0)
    parser.add_argument("--llm-timeout", type=float, default=90.0)
    parser.add_argument("--no-verify", action="store_true")
    parser.add_argument("--case-id", action="append", default=[])
    parser.add_argument("--mode", action="append", choices=MODES, default=[])
    args = parser.parse_args()

    selected = set(args.case_id)
    problems = [
        problem for problem in read_jsonl(args.cases)
        if not selected or problem.id in selected
    ]
    modes = tuple(args.mode) or MODES
    config = load_config(args.config)
    case_rows: list[dict[str, Any]] = []
    arm_rows: list[dict[str, Any]] = []
    for problem in problems:
        scouts = cheap_scouts(problem)
        h_eq = solver.parse_equation(problem.equation1)
        g_eq = solver.parse_equation(problem.equation2)
        features = stage1_features(h_eq, g_eq)
        answer_wing = "true" if problem.answer else "false"
        case_rows.append({
            "problem": problem.to_mapping(),
            "answer_wing": answer_wing,
            "stage1_prediction": features["prediction"],
            "stage1_correct": features["prediction"] == answer_wing,
            "scouts": scouts,
        })
        if scouts["true_candidate"] or scouts["false_candidate"]:
            continue
        for mode in modes:
            print(f"[{problem.id}] {mode}", flush=True)
            arm_rows.append(
                run_arm(
                    problem,
                    mode,
                    config,
                    scouts,
                    args.action_budget,
                    args.llm_timeout,
                    not args.no_verify,
                )
            )
            args.output.parent.mkdir(parents=True, exist_ok=True)
            partial = {
                "created_at": datetime.now(UTC).isoformat(),
                "config": {
                    "model": (config.get("llm") or {}).get("model"),
                    "base_url": (config.get("llm") or {}).get("base_url"),
                    "action_budget": args.action_budget,
                    "modes": list(modes),
                },
                "summary": summarize(case_rows, arm_rows),
                "cases": case_rows,
                "arms": arm_rows,
            }
            args.output.write_text(
                json.dumps(partial, ensure_ascii=False, indent=2) + "\n",
                encoding="utf-8",
            )

    result = {
        "created_at": datetime.now(UTC).isoformat(),
        "config": {
            "model": (config.get("llm") or {}).get("model"),
            "base_url": (config.get("llm") or {}).get("base_url"),
            "action_budget": args.action_budget,
            "modes": list(modes),
        },
        "summary": summarize(case_rows, arm_rows),
        "cases": case_rows,
        "arms": arm_rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(result["summary"], indent=2))
    print(f"wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
