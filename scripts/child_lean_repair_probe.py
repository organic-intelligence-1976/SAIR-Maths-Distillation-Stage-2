#!/usr/bin/env python3
"""Test bounded LLM Lean repair on an isolated, mechanically consumable midpoint."""

from __future__ import annotations

import argparse
from copy import deepcopy
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


def root_midpoint_candidate(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    *,
    consume_budget: float,
) -> tuple[baby_solver.UniversalEquation | None, str | None, list[dict[str, Any]]]:
    attempts: list[dict[str, Any]] = []
    for kind in baby_solver.implied_standard_aux_lemmas(h_eq):
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


def exact_h_fact_menu(
    h_eq: dict[str, Any],
    target_eq: dict[str, Any],
    *,
    limit: int = 24,
) -> list[str]:
    lines: list[str] = []
    for index, args in enumerate(
        baby_solver.candidate_h_args(h_eq, target_eq, limit),
        start=1,
    ):
        lhs, rhs = baby_solver.render_h_type(h_eq, args)
        call_args = " ".join(baby_solver.lean_arg(arg) for arg in args)
        lines.append(
            f"f{index}: `have f{index} := h {call_args}` gives `{lhs} = {rhs}`"
        )
    return lines


def focused_state(state: dict[str, Any]) -> dict[str, Any]:
    superposition = state.get("superposition_state")
    return {
        "status": state.get("status"),
        "target": state.get("target"),
        "left_frontier": list(state.get("left_frontier") or [])[:6],
        "right_frontier": list(state.get("right_frontier") or [])[:6],
        "closest_pairs": list(state.get("closest_pairs") or [])[:4],
        "need_hint": state.get("need_hint"),
        "closest_derived_equations": (
            list(superposition.get("closest_equations") or [])[:6]
            if isinstance(superposition, dict)
            else []
        ),
    }


def clean_child_body(raw: Any) -> tuple[str, list[dict[str, Any]]]:
    body = baby_solver.clean_body(str(raw or ""))
    repairs: list[dict[str, Any]] = []
    if body.startswith("by\n"):
        body = body[3:].lstrip()
        repairs.append({"kind": "removed_redundant_by"})
    elif body == "by":
        body = ""
    lines = body.splitlines()
    if lines:
        later_indents = [
            len(line) - len(line.lstrip())
            for line in lines[1:]
            if line.strip()
        ]
        if later_indents and min(later_indents) > 0:
            remove = min(later_indents)
            lines = [lines[0], *[
                line[remove:] if line.strip() else line
                for line in lines[1:]
            ]]
            body = "\n".join(lines)
            repairs.append({
                "kind": "dedented_trailing_body",
                "spaces": remove,
            })
    repaired_lines: list[str] = []
    for line_number, line in enumerate(body.splitlines(), start=1):
        prefix, separator, suffix = line.partition(":= by")
        if separator:
            missing = prefix.count("(") - prefix.count(")")
            if missing > 0:
                line = f"{prefix}{')' * missing} {separator}{suffix}"
                repairs.append({
                    "kind": "balanced_have_type_parentheses",
                    "line": line_number,
                    "inserted": missing,
                })
        repaired_lines.append(line)
    return "\n".join(repaired_lines), repairs


def parse_child_body(response: dict[str, Any]) -> tuple[str | None, dict[str, Any]]:
    data = baby_solver.extract_json(str(response.get("response") or ""))
    if not isinstance(data, dict):
        return None, {
            "status": "parse_failed",
            "error": response.get("error") or "no JSON object",
        }
    raw_body = data.get("proof") or data.get("body") or data.get("lean")
    body, syntax_repairs = clean_child_body(raw_body)
    if not body:
        return None, {
            "status": "missing_proof_body",
            "action": data,
        }
    return body, {
        "status": "parsed",
        "kind": data.get("kind"),
        "why": str(data.get("why") or "")[:500],
        "syntax_repairs": syntax_repairs,
    }


def verifier_feedback(record: dict[str, Any]) -> dict[str, Any]:
    return {
        "status": record.get("status"),
        "error_code": record.get("error_code"),
        "message": str(record.get("message") or "")[:7000],
        "stderr": str((record.get("details") or {}).get("stderr") or "")[:2500],
    }


def child_prompt(
    *,
    problem_id: str,
    h_eq: dict[str, Any],
    root: baby_solver.UniversalEquation,
    fact_menu: list[str],
    mechanical_state: dict[str, Any],
    round_index: int,
    previous_attempts: list[dict[str, Any]],
) -> str:
    h_statement = baby_solver.lemma_statement(h_eq)
    root_statement = baby_solver.lemma_statement(root.eq)
    prior = [
        {
            "round": attempt["round"],
            "proof": attempt.get("proof"),
            "verification": attempt.get("verification_feedback"),
        }
        for attempt in previous_attempts[-2:]
    ]
    return f"""You are repairing one isolated Lean proof obligation over an
arbitrary magma with operation ◇. Your output is untrusted and will be checked
by the official Lean verifier.

Problem: {problem_id}

Available hypothesis:
h : {h_statement}

Child target:
{root_statement}

The complete submission wrapper is:

```lean
import JudgeProblem

set_option maxHeartbeats 12800000 in
def submission : Goal := by
  intro G _ h
  have {root.name} : {root_statement} := by
    <YOUR CHILD PROOF BODY>
  <already mechanically verified proof of the original goal using {root.name}>
```

Prove only the child target. Your body should normally begin with
`intro {' '.join(root.eq['variables'])}`. You may use `h`, equality symmetry and
transitivity, `congrArg`, `rw`, `calc`, `simpa`, and Lean tactics. Do not assume
the child target or use it as a rewrite rule. Do not use `sorry`, `admit`, add
axioms, restate the target as an unproved `have`, or explain a mathematical step
that the Lean body does not perform.

This is an arbitrary magma: the operation is not injective, cancellative,
associative, or commutative. In particular, equality of `p ◇ r` and `q ◇ r`
does not imply `p = q`. `congrArg` may carry a proved equality into a context,
but it cannot cancel that context. A rewrite is valid only when Lean can match
the displayed pattern syntactically.

Exact examples of legal h-instantiations:
{chr(10).join(fact_menu)}

Mechanical search reached this state before asking you:
{json.dumps(mechanical_state, ensure_ascii=False)}

Previous rejected child proofs and exact Lean feedback:
{json.dumps(prior, ensure_ascii=False)}

This is repair round {round_index}. Return exactly one JSON object:
{{"kind":"child_proof","proof":"intro ...\\n...","why":"brief proof outline"}}
Keep the proof under 35 nonblank lines. Do not use markdown or include prose
outside the JSON object.
"""


def run_case(
    problem_id: str,
    *,
    llm_config: dict[str, Any],
    rounds: int,
    attain_budget: float,
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
        "attempts": list(prior_report.get("attempts") or [])
        if isinstance(prior_report, dict)
        else [],
        "solved": False,
    }
    if root is None or consume_body is None:
        report["outcome"] = "no_easy_root_midpoint"
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        return report

    mechanical_body, mechanical_state = baby_solver.prove_with_assumptions_detailed(
        h_eq,
        root.eq,
        [],
        superposition_budget=attain_budget,
    )
    report["baseline_child_status"] = "proved" if mechanical_body else "stuck"
    report["baseline_child_state"] = focused_state(mechanical_state)
    if mechanical_body is not None:
        final_body = (
            f"have {root.name} : {baby_solver.lemma_statement(root.eq)} := by\n"
            f"{baby_solver.indent(mechanical_body, 2)}\n"
            f"{consume_body}"
        )
        verification = verifier.verify(
            problem,
            ExecutionResult(status="candidate_ready", body=final_body),
        )
        report["verification"] = verification.to_mapping()
        report["solved"] = verification.accepted
        report["outcome"] = "baseline_child_proved"
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        return report

    fact_menu = exact_h_fact_menu(h_eq, root.eq)
    for attempt in report["attempts"]:
        body, syntax_repairs = clean_child_body(attempt.get("proof"))
        if not body:
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
        verification_mapping = verification.to_mapping()
        attempt["proof"] = body
        attempt["replay_syntax_repairs"] = syntax_repairs
        attempt["verification"] = verification_mapping
        attempt["verification_feedback"] = verifier_feedback(verification_mapping)
        if verification.accepted:
            report["solved"] = True
            report["outcome"] = "prior_child_proof_accepted_after_repair"
            report["winning_round"] = attempt.get("round")
            report["accepted_body"] = final_body
            report["elapsed_seconds"] = round(time.monotonic() - started, 3)
            return report

    for round_index in range(len(report["attempts"]) + 1, rounds + 1):
        prompt = child_prompt(
            problem_id=problem_id,
            h_eq=h_eq,
            root=root,
            fact_menu=fact_menu,
            mechanical_state=report["baseline_child_state"],
            round_index=round_index,
            previous_attempts=report["attempts"],
        )
        llm_started = time.monotonic()
        response = _call_llm(
            prompt,
            llm_config,
            max_seconds=llm_timeout,
        )
        body, adapter = parse_child_body(response)
        attempt: dict[str, Any] = {
            "round": round_index,
            "llm_seconds": round(time.monotonic() - llm_started, 3),
            "llm_error": response.get("error"),
            "adapter": adapter,
            "proof": body,
        }
        report["attempts"].append(attempt)
        if body is None:
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
        verification_mapping = verification.to_mapping()
        attempt["verification"] = verification_mapping
        attempt["verification_feedback"] = verifier_feedback(verification_mapping)
        if verification.accepted:
            report["solved"] = True
            report["outcome"] = "llm_child_proof_accepted"
            report["winning_round"] = round_index
            report["accepted_body"] = final_body
            break

    report.setdefault("outcome", "child_repair_rounds_exhausted")
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
        default=ROOT / ".artifacts" / "child_lean_repair_probe.json",
    )
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--attain-budget", type=float, default=10.0)
    parser.add_argument("--consume-budget", type=float, default=4.0)
    parser.add_argument("--llm-timeout", type=float, default=180.0)
    parser.add_argument("--max-output-tokens", type=int, default=24000)
    parser.add_argument("--judge-timeout", type=int, default=120)
    parser.add_argument(
        "--resume-report",
        type=Path,
        help="Continue from a prior probe, replaying stored bodies after syntax repair.",
    )
    args = parser.parse_args()

    config = deepcopy(load_config(str(args.llm_config)))
    config["llm"]["max_output_tokens"] = max(
        2000,
        min(65536, args.max_output_tokens),
    )
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
            rounds=max(1, min(5, args.rounds)),
            attain_budget=max(1.0, args.attain_budget),
            consume_budget=max(1.0, args.consume_budget),
            llm_timeout=max(5.0, args.llm_timeout),
            verifier=verifier,
            prior_report=prior_by_problem.get(problem_id),
        )
        for problem_id in (args.problem_id or ["hard3_0214", "hard3_0314"])
    ]
    payload = {
        "experiment": "bounded_llm_child_lean_repair",
        "controls": {
            "rounds": max(1, min(5, args.rounds)),
            "attain_budget": max(1.0, args.attain_budget),
            "consume_budget": max(1.0, args.consume_budget),
            "max_output_tokens": config["llm"]["max_output_tokens"],
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
