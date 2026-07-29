#!/usr/bin/env python3
"""Test one extra LLM-assisted recursion level on true midpoint obligations."""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
OFFICIAL = ROOT / "official-stage2"
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(OFFICIAL))

import baby_solver  # noqa: E402
from pipeline.proxy import _call_llm, load_config  # type: ignore  # noqa: E402
from research_system.curriculum import load_problem  # noqa: E402
from research_system.protocol import ExecutionResult  # noqa: E402
from research_system.verifier import OfficialLeanVerifier  # noqa: E402


def same_equation(left: dict[str, Any], right: dict[str, Any]) -> bool:
    return bool(
        (left["lhs"] == right["lhs"] and left["rhs"] == right["rhs"])
        or (left["lhs"] == right["rhs"] and left["rhs"] == right["lhs"])
    )


def root_midpoint_candidate(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    *,
    consume_budget: float,
) -> tuple[baby_solver.UniversalEquation | None, str | None, list[dict[str, Any]]]:
    """Find a standard helper that makes the second leg mechanically easy."""
    attempts: list[dict[str, Any]] = []
    plausible = baby_solver.implied_standard_aux_lemmas(h_eq)
    for kind in plausible:
        equation = baby_solver.standard_aux_equation(kind)
        midpoint = baby_solver.UniversalEquation(
            name=f"root_{kind}",
            eq=equation,
            extra_args=[],
        )
        body, state = baby_solver.prove_with_assumptions_detailed(
            h_eq,
            g_eq,
            [midpoint],
            superposition_budget=consume_budget,
        )
        attempts.append({
            "kind": kind,
            "equation": equation["text"],
            "consume_status": "proved" if body else "stuck",
            "consume_state": baby_solver.compact_feedback_value(
                state,
                string_limit=300,
            ),
        })
        if body:
            return midpoint, body, attempts
    return None, None, attempts


def recursive_prompt(
    problem_id: str,
    h_text: str,
    parent_midpoint_text: str,
    active_target_text: str,
    ancestor_target_texts: list[str],
    proved_assumptions: list[dict[str, Any]],
    feedback: dict[str, Any],
    *,
    round_index: int,
    previous_actions: list[dict[str, Any]],
) -> str:
    return f"""You are selecting intermediate universal equations for a trusted
mechanical equational prover over arbitrary magmas with operation ◇.

This is a depth-1 recursive proof obligation from problem {problem_id}.
The parent proof has already established mechanically that assuming midpoint M
is enough to prove the original goal:

H: {h_text}
M: {parent_midpoint_text}

The currently active recursive child is:

T: {active_target_text}

Both M and T are unproved ancestor targets. They are unavailable as rewrite
rules or assumptions, and they must not be returned as proposed lemmas. Only H,
the proved siblings listed below, and earlier mechanically proved Ni may be
used.

All unavailable ancestor targets:
{json.dumps(ancestor_target_texts, ensure_ascii=False)}

These sibling lemmas have already been mechanically proved from H and may be
used while proving T:
{json.dumps(proved_assumptions, ensure_ascii=False)}

The mechanical attempt to prove H plus those siblings => T is stuck. Propose a
short ordered chain N1, ..., Nk, with 1 <= k <= 5, such that each Ni is a
universal equation plausibly derivable from H, the proved siblings, and earlier
Nj, and the complete chain helps prove T.
Intermediate equations may be syntactically larger than M. Prefer equations
close to the derived/closest equations in the feedback. Useful patterns include
factor irrelevance, contraction, idempotence, absorption, and specialized
equations that can later yield a projection law.

Do not return T itself as the only lemma. Do not return a false-model action,
Lean code, prose outside JSON, or chain-of-thought.

Mechanical feedback:
{json.dumps(feedback, ensure_ascii=False)}

Previous recursive actions:
{json.dumps(previous_actions[-2:], ensure_ascii=False)}

This is recursive round {round_index}. Return exactly:
{{"kind":"midpoint_chain","lemmas":[
  {{"name":"n1","equation":"<universal equation>"}},
  {{"name":"n2","equation":"<universal equation>"}}
],"why":"brief explanation"}}
"""


def active_recursive_obligation(
    state: dict[str, Any],
    fallback_target: dict[str, Any],
) -> tuple[dict[str, Any], list[dict[str, Any]], dict[str, Any]]:
    proved = [
        item
        for item in state.get("proved_lemmas") or []
        if isinstance(item, dict) and item.get("equation")
    ]
    for failure in reversed(state.get("failed_midpoints") or []):
        if not isinstance(failure, dict) or not failure.get("equation"):
            continue
        try:
            target = baby_solver.parse_equation(str(failure["equation"]))
        except Exception:
            continue
        search_state = failure.get("search_state")
        return (
            target,
            proved,
            search_state if isinstance(search_state, dict) else state,
        )
    return fallback_target, proved, state


def parse_hints(
    response: dict[str, Any],
    forbidden_eqs: list[dict[str, Any]],
) -> tuple[dict[str, Any] | None, list[baby_solver.UniversalEquation], dict[str, Any] | None]:
    data = baby_solver.extract_json(str(response.get("response") or ""))
    if not isinstance(data, dict):
        return None, [], {
            "kind": "LLMAdapterState",
            "status": "parse_failed",
            "error": response.get("error") or "no JSON object",
        }
    normalized, adapter = baby_solver.normalize_llm_action(data)
    if normalized is None or not baby_solver.is_hint_payload(normalized):
        return normalized, [], adapter or {
            "kind": "LLMAdapterState",
            "status": "unsupported_recursive_action",
        }
    hints = [
        hint
        for hint in baby_solver.parse_universal_equations(normalized)
        if not any(same_equation(hint.eq, forbidden) for forbidden in forbidden_eqs)
    ][:5]
    return normalized, hints, adapter


def merge_hints(
    existing: list[baby_solver.UniversalEquation],
    additions: list[baby_solver.UniversalEquation],
) -> list[baby_solver.UniversalEquation]:
    out: list[baby_solver.UniversalEquation] = []
    signatures: set[str] = set()
    for hint in [*existing, *additions]:
        signature = min(
            f"{hint.eq['lhs']}={hint.eq['rhs']}",
            f"{hint.eq['rhs']}={hint.eq['lhs']}",
        )
        if signature in signatures:
            continue
        signatures.add(signature)
        out.append(baby_solver.UniversalEquation(
            name=f"submid_{len(out) + 1}",
            eq=hint.eq,
            extra_args=hint.extra_args,
        ))
    return out[-5:]


def run_case(
    problem_id: str,
    *,
    llm_config: dict[str, Any],
    llm_rounds: int,
    attain_budget: float,
    chain_budget: float,
    consume_budget: float,
    llm_timeout: float,
    verifier: OfficialLeanVerifier,
    prior_report: dict[str, Any] | None = None,
) -> dict[str, Any]:
    problem = load_problem(problem_id)
    h_eq = baby_solver.parse_equation(problem.equation1)
    g_eq = baby_solver.parse_equation(problem.equation2)
    started = time.monotonic()
    root, consume_body, consume_attempts = root_midpoint_candidate(
        h_eq,
        g_eq,
        consume_budget=consume_budget,
    )
    report: dict[str, Any] = {
        "problem_id": problem_id,
        "hypothesis": problem.equation1,
        "goal": problem.equation2,
        "consume_attempts": consume_attempts,
        "root_midpoint": root.eq["text"] if root else None,
        "root_consume_leg": "proved" if consume_body else "stuck",
        "rounds": [],
        "solved": False,
    }
    prior_rounds = (
        list(prior_report.get("rounds") or [])
        if isinstance(prior_report, dict)
        else []
    )
    report["rounds"] = prior_rounds
    if root is None or consume_body is None:
        report["outcome"] = "no_easy_root_midpoint"
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        return report

    attain_body, attain_state = baby_solver.prove_with_assumptions_detailed(
        h_eq,
        root.eq,
        [],
        superposition_budget=attain_budget,
    )
    report["baseline_attain_leg"] = "proved" if attain_body else "stuck"
    report["baseline_attain_state"] = baby_solver.compact_feedback_value(
        attain_state,
        string_limit=500,
    )
    if attain_body is not None:
        final_body = (
            f"have {root.name} : {baby_solver.lemma_statement(root.eq)} := by\n"
            f"{baby_solver.indent(attain_body, 2)}\n"
            f"{consume_body}"
        )
        verification = verifier.verify(
            problem,
            ExecutionResult(status="candidate_ready", body=final_body),
        )
        report["verification"] = verification.to_mapping()
        report["solved"] = verification.accepted
        report["outcome"] = "baseline_attain_proved"
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        return report

    accumulated: list[baby_solver.UniversalEquation] = []
    previous_actions: list[dict[str, Any]] = []
    for prior_round in prior_rounds:
        action = prior_round.get("action")
        if not isinstance(action, dict):
            continue
        previous_actions.append(action)
        normalized, _adapter = baby_solver.normalize_llm_action(action)
        if normalized is None or not baby_solver.is_hint_payload(normalized):
            continue
        prior_hints = [
            hint
            for hint in baby_solver.parse_universal_equations(normalized)
            if not same_equation(hint.eq, root.eq)
        ]
        accumulated = merge_hints(accumulated, prior_hints)
    feedback = (
        prior_rounds[-1].get("mechanical_state")
        if prior_rounds
        and isinstance(prior_rounds[-1].get("mechanical_state"), dict)
        else report["baseline_attain_state"]
    )
    for round_index in range(len(prior_rounds) + 1, llm_rounds + 1):
        active_target, proved_assumptions, focused_feedback = (
            active_recursive_obligation(feedback, root.eq)
        )
        ancestor_targets = [root.eq, active_target]
        for prior_round in report["rounds"]:
            prior_target_text = prior_round.get("active_target")
            if not prior_target_text:
                continue
            try:
                prior_target = baby_solver.parse_equation(str(prior_target_text))
            except Exception:
                continue
            if not any(
                same_equation(prior_target, existing)
                for existing in ancestor_targets
            ):
                ancestor_targets.append(prior_target)
        prompt = recursive_prompt(
            problem_id,
            problem.equation1,
            root.eq["text"],
            active_target["text"],
            [target["text"] for target in ancestor_targets],
            proved_assumptions,
            focused_feedback,
            round_index=round_index,
            previous_actions=previous_actions,
        )
        llm_started = time.monotonic()
        response = _call_llm(
            prompt,
            llm_config,
            max_seconds=llm_timeout,
        )
        action, hints, adapter = parse_hints(
            response,
            ancestor_targets,
        )
        if isinstance(action, dict):
            previous_actions.append(action)
        accumulated = merge_hints(accumulated, hints)
        round_record: dict[str, Any] = {
            "round": round_index,
            "llm_seconds": round(time.monotonic() - llm_started, 3),
            "llm_error": response.get("error"),
            "active_target": active_target["text"],
            "proved_assumptions": proved_assumptions,
            "action": action,
            "adapter_state": adapter,
            "new_hints": [hint.eq["text"] for hint in hints],
            "accumulated_hints": [hint.eq["text"] for hint in accumulated],
        }
        if not accumulated:
            round_record["mechanical_status"] = "no_parseable_submidpoints"
            report["rounds"].append(round_record)
            feedback = round_record
            continue

        body, state = baby_solver.generic_midpoint_chain_attempt(
            h_eq,
            root.eq,
            accumulated,
            budget_policy={
                "total_budget": chain_budget,
                "initial_grant": min(5.0, chain_budget),
                "grant_growth": 2.0,
                "max_grant": min(24.0, chain_budget),
                "max_grants_per_task": 4,
                "attain_priority": 1.2,
                "consume_priority": 1.0,
                "goal_priority": 1.1,
            },
        )
        round_record["mechanical_status"] = "proved" if body else "stuck"
        round_record["mechanical_state"] = baby_solver.compact_feedback_value(
            state,
            string_limit=600,
        )
        report["rounds"].append(round_record)
        if body is None:
            feedback = round_record["mechanical_state"]
            continue

        final_body = (
            f"have {root.name} : {baby_solver.lemma_statement(root.eq)} := by\n"
            f"{baby_solver.indent(body, 2)}\n"
            f"{consume_body}"
        )
        verification = verifier.verify(
            problem,
            ExecutionResult(status="candidate_ready", body=final_body),
        )
        round_record["verification"] = verification.to_mapping()
        if verification.accepted:
            report["solved"] = True
            report["outcome"] = "recursive_llm_attain_leg_proved"
            report["winning_round"] = round_index
            break
        feedback = {
            "kind": "LeanVerificationState",
            "status": verification.status,
            "message": verification.message,
            "details": verification.details,
        }

    report.setdefault("outcome", "recursive_rounds_exhausted")
    report["elapsed_seconds"] = round(time.monotonic() - started, 3)
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--problem-id",
        action="append",
        default=[],
        help="Official problem ID; defaults to the two current true residuals.",
    )
    parser.add_argument(
        "--llm-config",
        type=Path,
        default=ROOT / ".artifacts" / "full_verification" / "openrouter_config.json",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / ".artifacts" / "recursive_midpoint_probe.json",
    )
    parser.add_argument("--llm-rounds", type=int, default=2)
    parser.add_argument("--attain-budget", type=float, default=10.0)
    parser.add_argument("--chain-budget", type=float, default=80.0)
    parser.add_argument("--consume-budget", type=float, default=4.0)
    parser.add_argument("--llm-timeout", type=float, default=120.0)
    parser.add_argument("--judge-timeout", type=int, default=120)
    parser.add_argument(
        "--resume-report",
        type=Path,
        help="Continue cases from a prior recursive probe without repeating LLM rounds.",
    )
    args = parser.parse_args()

    config = load_config(str(args.llm_config))
    verifier = OfficialLeanVerifier(timeout_seconds=args.judge_timeout)
    prior_by_problem: dict[str, dict[str, Any]] = {}
    if args.resume_report is not None:
        prior_payload = json.loads(args.resume_report.read_text(encoding="utf-8"))
        prior_by_problem = {
            str(report.get("problem_id")): report
            for report in prior_payload.get("reports") or []
            if isinstance(report, dict) and report.get("problem_id")
        }
    started = time.monotonic()
    reports = [
        run_case(
            problem_id,
            llm_config=config,
            llm_rounds=max(1, min(5, args.llm_rounds)),
            attain_budget=max(1.0, args.attain_budget),
            chain_budget=max(5.0, args.chain_budget),
            consume_budget=max(1.0, args.consume_budget),
            llm_timeout=max(5.0, args.llm_timeout),
            verifier=verifier,
            prior_report=prior_by_problem.get(problem_id),
        )
        for problem_id in (args.problem_id or ["hard3_0214", "hard3_0314"])
    ]
    payload = {
        "experiment": "depth_1_llm_recursive_midpoint",
        "controls": {
            "llm_rounds": max(1, min(5, args.llm_rounds)),
            "attain_budget": max(1.0, args.attain_budget),
            "chain_budget_per_round": max(5.0, args.chain_budget),
            "consume_budget": max(1.0, args.consume_budget),
        },
        "reports": reports,
        "solved": sum(bool(report.get("solved")) for report in reports),
        "total": len(reports),
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(payload, indent=2, ensure_ascii=False))
    return 0 if payload["solved"] == payload["total"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
