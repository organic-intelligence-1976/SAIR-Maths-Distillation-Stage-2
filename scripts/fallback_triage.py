#!/usr/bin/env python3
"""Triage reference mechanical fallback wins with an LLM-first tie-breaker.

Input is the JSON summary from scripts/attribution_report.py. The output is an
action queue. The policy is intentionally biased toward LLM/mechanical
orchestration when the missing move can plausibly be expressed as a midpoint,
lemma chain, route choice, or repair. Native reference mechanical imports are
recommended first only when the missing capability looks like a mechanical
consumer gap.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


TRUE_NATIVE_PREFIXES = ("native:true", "native_reference")
FALSE_NATIVE_PREFIXES = ("native:false",)
PARTIAL_NATIVE_ROUTES = (
    "deep_saturation",
    "goal_superposition",
    "standard_aux_superposition",
    "proof_battery",
)


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def attempted_categories(row: dict[str, Any]) -> set[str]:
    return {
        str(attempt.get("category"))
        for attempt in row.get("attempted_routes") or []
        if isinstance(attempt, dict)
    }


def attempted_routes(row: dict[str, Any]) -> list[str]:
    return [
        str(attempt.get("route"))
        for attempt in row.get("attempted_routes") or []
        if isinstance(attempt, dict) and attempt.get("route")
    ]


def route_startswith(route: str, prefixes: tuple[str, ...]) -> bool:
    return any(route.startswith(prefix) for prefix in prefixes)


def classify_child_winner(row: dict[str, Any]) -> dict[str, Any]:
    verdict = str(row.get("verdict") or "")
    routes = attempted_routes(row)
    categories = attempted_categories(row)
    native_true_attempted = any(route_startswith(route, TRUE_NATIVE_PREFIXES) for route in routes)
    native_false_attempted = any(route_startswith(route, FALSE_NATIVE_PREFIXES) for route in routes)
    llm_attempted = "llm_load_bearing" in categories

    if verdict == "true":
        if native_true_attempted:
            first = "llm_orchestration_probe"
            why = (
                "A trusted true-side consumer was already attempted before the child fallback won. "
                "First ask whether the child proof can be represented as a smaller midpoint, "
                "lemma_chain, or repair that existing subgoal-capable tools can verify."
            )
            fallback = "native_import_if_probe_fails"
            import_target = "the specific child proof component, likely broad certificates, saturation, or superposition scheduling"
        else:
            first = "native_import_probe"
            why = (
                "No native true-side attempt was visible before the child fallback won. "
                "Expose the responsible reference mechanical component as a protocol tool, then test LLM routing to it."
            )
            fallback = "llm_orchestration_after_tool_exists"
            import_target = "child true-side winner"
    elif verdict == "false":
        if native_false_attempted:
            first = "llm_orchestration_probe"
            why = (
                "False-search routes were already attempted before the child fallback won. "
                "First test whether better route feedback, seed/size repair, or a false_model_hint "
                "lets the LLM select the missing witness family."
            )
            fallback = "native_import_if_probe_fails"
            import_target = "the specific reference mechanical counterexample family or model-finder route"
        else:
            first = "native_import_probe"
            why = (
                "No native false route was visible before the child fallback won. "
                "Expose the child witness family as a named false_model_search route."
            )
            fallback = "llm_orchestration_after_route_exists"
            import_target = "child false-side witness family"
    else:
        first = "inspect_manually"
        why = "The fallback winner lacks a clear verdict; rerun with attribution/logging."
        fallback = "rerun"
        import_target = "unknown"

    if llm_attempted:
        why += " An LLM attempt is already present, so compare its feedback before adding prompt examples."

    return {
        "problem_id": row.get("id"),
        "verdict": verdict,
        "winning_route": row.get("route"),
        "first_action": first,
        "fallback_action": fallback,
        "import_target_if_needed": import_target,
        "why": why,
        "attempted_routes_tail": routes[-8:],
        "artifact": row.get("artifact"),
    }


def classify_failed_child_attempt(row: dict[str, Any]) -> dict[str, Any]:
    verdicts = [route for route in attempted_routes(row) if route.startswith("child_reference")]
    return {
        "problem_id": row.get("id"),
        "status": "child_attempt_failed",
        "first_action": "do_not_import_from_this_case_yet",
        "why": (
            "The child fallback was tried but did not solve, so this is not evidence "
            "for a missing reference mechanical native component. Use the mechanical stuck state to "
            "choose a next-frontier LLM or false-consumer experiment instead."
        ),
        "child_routes": verdicts,
        "artifact": row.get("artifact"),
    }


def classify_orchestration_candidate(row: dict[str, Any]) -> dict[str, Any] | None:
    if row.get("solved"):
        return None
    routes = attempted_routes(row)
    partial = [route for route in routes if route.startswith(PARTIAL_NATIVE_ROUTES)]
    if not partial:
        return None
    llm_calls = int(row.get("llm_calls") or 0)
    return {
        "problem_id": row.get("id"),
        "status": "native_partial_failed",
        "first_action": "llm_orchestration_probe",
        "why": (
            "A partially imported reference mechanical route was attempted but did not solve. "
            "Before importing more machinery, expose that failed route as feedback "
            "and test whether the LLM can propose a midpoint, lemma_chain, seed_args, "
            "or route repair that existing consumers can verify."
        ),
        "partial_native_routes": partial[-6:],
        "llm_calls": llm_calls,
        "fallback_action": "native_import_only_if_llm_probe_fails",
        "artifact": row.get("artifact"),
    }


def build_triage(summary: dict[str, Any]) -> dict[str, Any]:
    rows = summary.get("rows") or []
    child_winners = summary.get("child_reference_winners") or []
    failed_child_attempts = summary.get("failed_child_attempts") or []
    actions = [classify_child_winner(row) for row in child_winners if isinstance(row, dict)]
    failed = [classify_failed_child_attempt(row) for row in failed_child_attempts if isinstance(row, dict)]
    orchestration = [
        item
        for row in rows
        if isinstance(row, dict)
        for item in [classify_orchestration_candidate(row)]
        if item is not None
    ]
    return {
        "policy": "Prefer LLM orchestration when the missing move can plausibly be expressed as a midpoint, lemma chain, route choice, or repair; import reference mechanical natively when the consumer itself is missing.",
        "child_winner_count": len(actions),
        "failed_child_attempt_count": len(failed),
        "orchestration_candidate_count": len(orchestration),
        "actions": actions,
        "orchestration_candidates": orchestration,
        "failed_child_attempts": failed,
        "next_step": (
            "Run the first action for the first child winner."
            if actions
            else "Run the first LLM-orchestration probe for a partial native failure."
            if orchestration
            else "No child-fallback winners or partial-native failures found; expand the attribution slice before importing more reference mechanical machinery."
        ),
    }


def write_markdown(result: dict[str, Any], path: Path) -> None:
    lines = [
        "# Fallback Triage",
        "",
        "Generated by `scripts/fallback_triage.py`.",
        "",
        f"Policy: {result['policy']}",
        "",
        f"- Child fallback winners: `{result['child_winner_count']}`",
        f"- Partial-native orchestration candidates: `{result['orchestration_candidate_count']}`",
        f"- Failed child attempts: `{result['failed_child_attempt_count']}`",
        f"- Next step: {result['next_step']}",
        "",
    ]
    if result["actions"]:
        lines.extend(["## Action Queue", ""])
        for action in result["actions"]:
            lines.append(f"### {action['problem_id']}")
            lines.append("")
            lines.append(f"- Verdict: `{action['verdict']}`")
            lines.append(f"- First action: `{action['first_action']}`")
            lines.append(f"- Fallback action: `{action['fallback_action']}`")
            lines.append(f"- Import target if needed: {action['import_target_if_needed']}")
            lines.append(f"- Why: {action['why']}")
            lines.append(f"- Attempt tail: `{json.dumps(action['attempted_routes_tail'], ensure_ascii=False)}`")
            lines.append("")
    if result["orchestration_candidates"]:
        lines.extend(["## LLM-Orchestration Candidates", ""])
        for item in result["orchestration_candidates"]:
            lines.append(f"### {item['problem_id']}")
            lines.append("")
            lines.append(f"- First action: `{item['first_action']}`")
            lines.append(f"- Fallback action: `{item['fallback_action']}`")
            lines.append(f"- Partial native routes: `{json.dumps(item['partial_native_routes'], ensure_ascii=False)}`")
            lines.append(f"- LLM calls in run: `{item['llm_calls']}`")
            lines.append(f"- Why: {item['why']}")
            lines.append("")
    if result["failed_child_attempts"]:
        lines.extend(["## Failed Child Attempts", ""])
        for item in result["failed_child_attempts"]:
            lines.append(f"- `{item['problem_id']}`: {item['why']}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("summary", type=Path, help="JSON output from scripts/attribution_report.py")
    parser.add_argument("--json-output", type=Path, default=None)
    parser.add_argument("--markdown-output", type=Path, default=None)
    args = parser.parse_args()

    result = build_triage(load_json(args.summary))
    if args.json_output:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")
    if args.markdown_output:
        write_markdown(result, args.markdown_output)
    print(json.dumps({
        "child_winner_count": result["child_winner_count"],
        "orchestration_candidate_count": result["orchestration_candidate_count"],
        "failed_child_attempt_count": result["failed_child_attempt_count"],
        "next_step": result["next_step"],
    }, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
