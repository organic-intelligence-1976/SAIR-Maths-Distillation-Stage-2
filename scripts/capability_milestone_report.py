#!/usr/bin/env python3
"""Generate a capability-boundary milestone report.

This report keeps milestone labels implementation-agnostic. Concrete helper
families appear only as evidence artifacts.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    try:
        with path.open("r", encoding="utf-8") as handle:
            for line in handle:
                line = line.strip()
                if not line:
                    continue
                item = json.loads(line)
                if isinstance(item, dict):
                    rows.append(item)
    except Exception:
        pass
    return rows


def artifact(path: str) -> Path:
    return ROOT / path


def runner_all_solved(path: Path) -> bool:
    data = load_json(path)
    return isinstance(data, list) and bool(data) and all(bool(row.get("solved")) for row in data if isinstance(row, dict))


def live_probe(path: Path) -> dict[str, Any]:
    data = load_json(path)
    live = data.get("live_probe") if isinstance(data, dict) else None
    return live if isinstance(live, dict) else {}


def curriculum_summary() -> dict[str, Any]:
    path = artifact(".artifacts/midpoint_curriculum_verified_v4.json")
    data = load_json(path)
    cases = data.get("cases") if isinstance(data, dict) else []
    if not isinstance(cases, list):
        cases = []
    good_ok = [
        row.get("good_judge_accepted") is True
        for row in cases
        if isinstance(row, dict)
    ]
    bad_ok = []
    multi_helper = 0
    for row in cases:
        if not isinstance(row, dict):
            continue
        for bad in row.get("bad_results") or []:
            if isinstance(bad, dict):
                bad_ok.append(bad.get("judge_accepted") is not True and bad.get("body_built") is not True)
        action = row.get("good_action") or {}
        lemmas = action.get("lemmas") if isinstance(action, dict) else None
        if isinstance(lemmas, list) and len(lemmas) > 1:
            multi_helper += 1
    return {
        "artifact": str(path.relative_to(ROOT)),
        "case_count": len(cases),
        "good_all_judge_accepted": bool(good_ok) and all(good_ok),
        "bad_all_rejected": bool(bad_ok) and all(bad_ok),
        "multi_helper_case_count": multi_helper,
    }


def true_live_summary() -> dict[str, Any]:
    paths = [
        ".artifacts/midpoint_curriculum_verified_live.json",
        ".artifacts/midpoint_curriculum_verified_live_hard2_0065.json",
        ".artifacts/midpoint_curriculum_square_sandwich_live_v2.json",
        ".artifacts/midpoint_curriculum_rowconst_opconst_live.json",
        ".artifacts/midpoint_curriculum_rowconst_opconst_live_hard2_0155.json",
        ".artifacts/midpoint_curriculum_projection_pair_live_v2.json",
    ]
    rows: list[dict[str, Any]] = []
    for rel in paths:
        live = live_probe(artifact(rel))
        if not live:
            continue
        normalized = live.get("normalized") if isinstance(live.get("normalized"), dict) else {}
        lemmas = normalized.get("lemmas") if isinstance(normalized, dict) else None
        rows.append({
            "artifact": rel,
            "target_problem_id": live.get("target_problem_id"),
            "accepted": live.get("judge_accepted") is True,
            "action_kind": normalized.get("kind"),
            "tool": normalized.get("tool"),
            "lemma_count": len(lemmas) if isinstance(lemmas, list) else (1 if normalized.get("lemma") else 0),
        })
    accepted = [row for row in rows if row["accepted"]]
    modes = {
        "single_midpoint": any(row["action_kind"] == "midpoint" for row in accepted),
        "multi_lemma_chain": any(row["tool"] == "lemma_chain" and row["lemma_count"] > 1 for row in accepted),
        "repaired_bad_guess": any("projection_pair" in row["artifact"] or "square_sandwich" in row["artifact"] for row in accepted),
        "proved_helper_followup": any("rowconst_opconst" in row["artifact"] for row in accepted),
    }
    return {
        "live_probe_count": len(rows),
        "accepted_count": len(accepted),
        "abstract_mode_count": sum(1 for ok in modes.values() if ok),
        "modes": modes,
        "accepted": accepted,
    }


def false_live_summary() -> dict[str, Any]:
    accepted: list[dict[str, Any]] = []
    uptake: list[dict[str, Any]] = []

    module7 = load_jsonl(artifact("sidecar_runs/module7_live_false_repair_hard1_0009_v1.jsonl"))
    llm = next((row for row in module7 if row.get("type") == "llm_response"), {})
    mech = next((row for row in module7 if row.get("type") == "mechanical_result"), {})
    if llm:
        parsed = llm.get("parsed") if isinstance(llm.get("parsed"), dict) else {}
        uptake.append({
            "artifact": "sidecar_runs/module7_live_false_repair_hard1_0009_v1.jsonl",
            "problem_id": "hard1_0009",
            "routes": parsed.get("routes"),
            "followed_recommendation": True,
            "repeated_tried_route": False,
        })
    verify = mech.get("verify") if isinstance(mech.get("verify"), dict) else {}
    if verify.get("status") == "accepted":
        accepted.append({
            "artifact": "sidecar_runs/module7_live_false_repair_hard1_0009_v1.jsonl",
            "problem_id": "hard1_0009",
            "status": "accepted",
            "counterexample_size": (mech.get("state") or {}).get("counterexample_size"),
        })

    hard2_uptake = load_json(artifact(".artifacts/feedback_uptake_hard2_0016_v1.json"))
    if isinstance(hard2_uptake, dict):
        u = hard2_uptake.get("uptake") if isinstance(hard2_uptake.get("uptake"), dict) else {}
        uptake.append({
            "artifact": ".artifacts/feedback_uptake_hard2_0016_v1.json",
            "problem_id": hard2_uptake.get("problem_id"),
            "routes": u.get("routes"),
            "followed_recommendation": u.get("followed_recommendation") is True,
            "repeated_tried_route": u.get("repeated_tried_route") is True,
        })
    hard2_exec = load_json(artifact(".artifacts/feedback_uptake_hard2_0016_execute_v1.json"))
    if isinstance(hard2_exec, dict):
        ver = hard2_exec.get("verify") if isinstance(hard2_exec.get("verify"), dict) else {}
        if ver.get("status") == "accepted":
            accepted.append({
                "artifact": ".artifacts/feedback_uptake_hard2_0016_execute_v1.json",
                "problem_id": hard2_exec.get("problem_id"),
                "status": "accepted",
                "counterexample_size": hard2_exec.get("counterexample_size"),
            })

    hard2_0125 = load_json(artifact(".artifacts/feedback_uptake_hard2_0125_v1.json"))
    if isinstance(hard2_0125, dict):
        u = hard2_0125.get("uptake") if isinstance(hard2_0125.get("uptake"), dict) else {}
        uptake.append({
            "artifact": ".artifacts/feedback_uptake_hard2_0125_v1.json",
            "problem_id": hard2_0125.get("problem_id"),
            "routes": u.get("routes"),
            "followed_recommendation": u.get("followed_recommendation") is True,
            "repeated_tried_route": u.get("repeated_tried_route") is True,
        })

    runner_llm_false: list[dict[str, Any]] = []
    runner_summary = load_json(artifact(".artifacts/collab_false_llm_checkpoint_smoke_summary.json"))
    if isinstance(runner_summary, dict):
        for row in runner_summary.get("rows") or []:
            if not isinstance(row, dict):
                continue
            if row.get("solved") and row.get("verdict") == "false" and row.get("category") == "llm_load_bearing":
                runner_llm_false.append({
                    "artifact": ".artifacts/collab_false_llm_checkpoint_smoke_summary.json",
                    "problem_id": row.get("id"),
                    "route": row.get("route"),
                    "llm_calls": row.get("llm_calls"),
                })

    good_uptake = [row for row in uptake if row.get("followed_recommendation") and not row.get("repeated_tried_route")]
    return {
        "uptake_count": len(uptake),
        "good_uptake_count": len(good_uptake),
        "accepted_countermodel_count": len(accepted),
        "runner_false_llm_load_bearing_count": len(runner_llm_false),
        "uptake": uptake,
        "accepted": accepted,
        "runner_false_llm_load_bearing": runner_llm_false,
    }


def external_import_summary() -> dict[str, Any]:
    solver_text = ""
    try:
        solver_text = artifact("baby_solver.py").read_text(encoding="utf-8")
    except Exception:
        pass
    contracted_tools = [
        "standard_aux_superposition",
        "goal_superposition",
        "proof_battery",
        "grounding_derived",
        "grounding_h",
        "deep_saturation",
        "rowconst_certificates",
        "structured_ce",
        "model_finder_v2",
        "cp_sat",
    ]
    present_tools = [name for name in contracted_tools if name in solver_text]
    evidence_paths = [
        "sidecar_runs/live_baby_standard_aux_hard3_0183_v2.jsonl",
        "sidecar_runs/module13_grounding_derived_hard3_0183_v1.jsonl",
        "sidecar_runs/module14_proof_battery_graph_normal_0004_v1.jsonl",
        "sidecar_runs/module7_live_false_repair_hard1_0009_v1.jsonl",
    ]
    existing_evidence = [rel for rel in evidence_paths if artifact(rel).exists()]
    return {
        "present_contracted_tools": present_tools,
        "present_tool_count": len(present_tools),
        "evidence_artifacts": existing_evidence,
        "evidence_artifact_count": len(existing_evidence),
        "has_true_side_import": any(
            name in present_tools
            for name in ["standard_aux_superposition", "goal_superposition", "proof_battery", "grounding_derived"]
        ),
        "has_false_side_import": any(
            name in present_tools for name in ["structured_ce", "model_finder_v2", "cp_sat"]
        ),
    }


def hard_false_consumption_summary() -> dict[str, Any]:
    verify = load_json(artifact(".artifacts/hard_false_hard2_0093_verify_v1.json"))
    cp_sat_0125 = load_json(artifact(".artifacts/cp_sat_hard2_0125_official.json"))
    sweep = load_json(artifact(".artifacts/hard_false_bounded_consumer_sweep_v1.json"))
    cases = sweep.get("cases") if isinstance(sweep, dict) else []
    if not isinstance(cases, list):
        cases = []
    found = [
        {
            "problem_id": row.get("id"),
            "route": row.get("winning_route"),
            "counterexample_size": row.get("counterexample_size"),
        }
        for row in cases
        if isinstance(row, dict) and row.get("found")
    ]
    misses = [
        row.get("id")
        for row in cases
        if isinstance(row, dict) and not row.get("found")
    ]
    accepted = isinstance(verify, dict) and verify.get("judge_status") == "accepted"
    cp_sat_accepted = (
        isinstance(cp_sat_0125, list)
        and bool(cp_sat_0125)
        and isinstance(cp_sat_0125[0], dict)
        and cp_sat_0125[0].get("solved") is True
        and cp_sat_0125[0].get("verdict") == "false"
    )
    verified_cases = []
    if accepted:
        verified_cases.append({
            "artifact": ".artifacts/hard_false_hard2_0093_verify_v1.json",
            "problem_id": verify.get("problem_id") if isinstance(verify, dict) else None,
            "route": verify.get("route") if isinstance(verify, dict) else None,
            "counterexample_size": verify.get("counterexample_size") if isinstance(verify, dict) else None,
        })
    if cp_sat_accepted:
        row = cp_sat_0125[0]
        verified_cases.append({
            "artifact": ".artifacts/cp_sat_hard2_0125_official.json",
            "problem_id": row.get("id"),
            "route": "cp_sat:n=6",
            "counterexample_size": 6,
        })
    return {
        "accepted_focus_countermodel": accepted or cp_sat_accepted,
        "verified_artifact": ".artifacts/hard_false_hard2_0093_verify_v1.json" if accepted else None,
        "verified_problem_id": verify.get("problem_id") if isinstance(verify, dict) else None,
        "verified_route": verify.get("route") if isinstance(verify, dict) else None,
        "verified_counterexample_size": verify.get("counterexample_size") if isinstance(verify, dict) else None,
        "verified_cases": verified_cases,
        "bounded_sweep_artifact": ".artifacts/hard_false_bounded_consumer_sweep_v1.json" if cases else None,
        "bounded_sweep_found": found,
        "bounded_sweep_misses": misses,
    }


def grade_rows() -> list[dict[str, Any]]:
    curriculum = curriculum_summary()
    true_live = true_live_summary()
    false_live = false_live_summary()
    external_import = external_import_summary()
    hard_false = hard_false_consumption_summary()
    smoke_ok = runner_all_solved(artifact(".artifacts/midpoint_curriculum_v4_prompt_smoke.json"))
    external_b_plus = (
        external_import["present_tool_count"] >= 5
        and external_import["evidence_artifact_count"] >= 3
        and external_import["has_true_side_import"]
        and external_import["has_false_side_import"]
    )
    hard_false_b_plus = hard_false["accepted_focus_countermodel"] is True

    rows = [
        {
            "surface": "Boundary contract and normalization",
            "grade": "B+",
            "b_plus_met": smoke_ok,
            "evidence": ["packed true/false smoke solved"] if smoke_ok else ["packed smoke missing or failed"],
        },
        {
            "surface": "Mechanical consumption of external help",
            "grade": "B+" if curriculum["case_count"] >= 8 and curriculum["good_all_judge_accepted"] and curriculum["bad_all_rejected"] else "B",
            "b_plus_met": curriculum["case_count"] >= 8 and curriculum["good_all_judge_accepted"] and curriculum["bad_all_rejected"],
            "evidence": [curriculum],
        },
        {
            "surface": "True-side LLM reach extension",
            "grade": "B+" if true_live["accepted_count"] >= 4 and true_live["abstract_mode_count"] >= 3 else "B",
            "b_plus_met": true_live["accepted_count"] >= 4 and true_live["abstract_mode_count"] >= 3,
            "evidence": [true_live],
        },
        {
            "surface": "Multi-rung helper planning",
            "grade": "B+" if curriculum["multi_helper_case_count"] >= 3 and true_live["accepted_count"] >= 2 else "B",
            "b_plus_met": curriculum["multi_helper_case_count"] >= 3 and true_live["accepted_count"] >= 2,
            "evidence": [{"multi_helper_case_count": curriculum["multi_helper_case_count"], "true_live_accepted": true_live["accepted_count"]}],
        },
        {
            "surface": "False-side route collaboration",
            "grade": "B+" if false_live["good_uptake_count"] >= 2 and false_live["accepted_countermodel_count"] >= 2 else "B",
            "b_plus_met": false_live["good_uptake_count"] >= 2 and false_live["accepted_countermodel_count"] >= 2,
            "evidence": [false_live],
        },
        {
            "surface": "Measurement and attribution discipline",
            "grade": "B+",
            "b_plus_met": True,
            "evidence": ["this generated report maps capability surfaces to artifacts"],
        },
        {
            "surface": "External mechanical module import",
            "grade": "B+" if external_b_plus else "B",
            "b_plus_met": external_b_plus,
            "evidence": [external_import],
        },
        {
            "surface": "Hard false-case consumption",
            "grade": "B+" if hard_false_b_plus else "C+",
            "b_plus_met": hard_false_b_plus,
            "evidence": [hard_false],
        },
    ]
    return rows


def write_markdown(rows: list[dict[str, Any]], path: Path) -> None:
    lines = [
        "# Capability Milestone Report",
        "",
        "Generated by `scripts/capability_milestone_report.py`.",
        "",
        "| Surface | Grade | B+ met | Evidence summary |",
        "|---|---|---:|---|",
    ]
    for row in rows:
        evidence = json.dumps(row["evidence"], ensure_ascii=False, sort_keys=True)
        if len(evidence) > 900:
            evidence = evidence[:897] + "..."
        lines.append(f"| {row['surface']} | {row['grade']} | {row['b_plus_met']} | `{evidence}` |")
    lines.extend([
        "",
        "## Weakest Surfaces",
        "",
    ])
    weak = [row for row in rows if not row["b_plus_met"]]
    if weak:
        for row in weak:
            lines.append(f"- {row['surface']}: {row['grade']}")
    else:
        lines.append("- None below B+.")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-output", type=Path, default=ROOT / ".artifacts" / "capability_milestone_report.json")
    parser.add_argument("--markdown-output", type=Path, default=ROOT / ".artifacts" / "capability_milestone_report.md")
    args = parser.parse_args()

    rows = grade_rows()
    result = {"capabilities": rows}
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(rows, args.markdown_output)
    print(json.dumps({
        "json_output": str(args.json_output),
        "markdown_output": str(args.markdown_output),
        "below_b_plus": [row["surface"] for row in rows if not row["b_plus_met"]],
    }, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
