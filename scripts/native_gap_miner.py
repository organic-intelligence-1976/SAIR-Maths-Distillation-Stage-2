#!/usr/bin/env python3
"""Mine capability gaps between the standalone solver and a reference solver.

The intended loop is:

1. package the source-independent solver from `baby_solver.py`;
2. run it and an optional historical/external reference on the same corpus;
3. identify rows where the reference solves and the standalone solver does not;
4. classify those gaps into mechanism buckets;
5. rank the buckets by estimated native-development ROI.

This is a development-planning harness, not a competition benchmark.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
OFFICIAL = ROOT / "official-stage2"

sys.path.insert(0, str(ROOT))
from scripts.attribution_report import summarize_row  # noqa: E402


def read_problem_rows(path: Path) -> list[dict[str, Any]]:
    text = path.read_text(encoding="utf-8")
    if text.lstrip().startswith("["):
        data = json.loads(text)
        return [row for row in data if isinstance(row, dict)]
    rows: list[dict[str, Any]] = []
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        row = json.loads(line)
        if isinstance(row, dict):
            rows.append(row)
    return rows


def read_problem_ids(path: Path) -> list[str]:
    return [str(row.get("id")) for row in read_problem_rows(path)]


def parse_id_filters(values: list[str] | None) -> set[str]:
    ids: set[str] = set()
    for value in values or []:
        for item in value.split(","):
            item = item.strip()
            if item:
                ids.add(item)
    return ids


def prepare_effective_problems(
    path: Path,
    work_dir: Path,
    *,
    ids: set[str],
    max_problems: int | None,
) -> Path:
    if not ids and max_problems is None:
        return path
    rows = read_problem_rows(path)
    if ids:
        rows = [row for row in rows if str(row.get("id")) in ids]
    if max_problems is not None:
        rows = rows[:max_problems]
    if not rows:
        raise ValueError("problem filter selected zero rows")
    out = work_dir / "effective_problems.jsonl"
    out.write_text(
        "\n".join(json.dumps(row, ensure_ascii=False) for row in rows) + "\n",
        encoding="utf-8",
    )
    return out


def replace_function_with_stub(source: str, func_name: str, stub: str) -> str:
    import ast

    module = ast.parse(source)
    target = None
    for node in module.body:
        if isinstance(node, ast.FunctionDef) and node.name == func_name:
            target = node
            break
    if target is None or target.end_lineno is None:
        raise ValueError(f"could not locate complete function {func_name}")
    lines = source.splitlines()
    start = target.lineno - 1
    end = target.end_lineno
    replacement = stub.rstrip().splitlines()
    return "\n".join(lines[:start] + replacement + lines[end:]) + "\n"


def prepare_submission_from_solver(
    solver_file: Path,
    dest: Path,
    *,
    disable_child_fallback: bool,
) -> Path:
    dest.mkdir(parents=True, exist_ok=True)
    for child in dest.iterdir():
        if child.is_dir():
            shutil.rmtree(child)
        else:
            child.unlink()
    source = solver_file.read_text(encoding="utf-8")
    if disable_child_fallback:
        retired_markers = (
            "REFERENCE_SOLVER_B64_ZLIB",
            "reference_namespace",
            "run_reference_mechanical_tool",
            "child_reference",
        )
        present = [marker for marker in retired_markers if marker in source]
        if present:
            raise ValueError(
                "solver is not source-independent; retired fallback markers remain: "
                + ", ".join(present)
            )
    (dest / "solver.py").write_text(source, encoding="utf-8")
    return dest


def prepare_submission_from_dir(src: Path, dest: Path) -> Path:
    dest.mkdir(parents=True, exist_ok=True)
    for child in dest.iterdir():
        if child.is_dir():
            shutil.rmtree(child)
        else:
            child.unlink()
    solver = src / "solver.py"
    if not solver.exists():
        raise ValueError(f"{src} does not contain solver.py")
    shutil.copy2(solver, dest / "solver.py")
    return dest


def run_pipeline(
    submission: Path,
    problems: Path,
    config: Path,
    output: Path,
    *,
    timeout: float,
) -> list[dict[str, Any]]:
    if output.exists():
        output.unlink()
    env = dict(os.environ)
    existing = env.get("PYTHONPATH")
    env["PYTHONPATH"] = str(OFFICIAL) if not existing else f"{OFFICIAL}{os.pathsep}{existing}"
    cmd = [
        sys.executable,
        "-m",
        "pipeline.runner",
        "--submission",
        str(submission),
        "--problems",
        str(problems),
        "--config",
        str(config),
        "--output",
        str(output),
    ]
    proc = subprocess.run(
        cmd,
        cwd=str(ROOT),
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"pipeline failed for {submission}:\n{proc.stdout[-4000:]}")
    if not output.exists():
        raise RuntimeError(f"pipeline did not write {output}:\n{proc.stdout[-4000:]}")
    return json.loads(output.read_text(encoding="utf-8"))


def attach_artifacts(rows: list[dict[str, Any]], artifact: Path) -> list[dict[str, Any]]:
    out = []
    for row in rows:
        if isinstance(row, dict):
            item = dict(row)
            item["_artifact"] = str(artifact)
            out.append(item)
    return out


def summary_by_id(rows: list[dict[str, Any]], artifact: Path) -> dict[str, dict[str, Any]]:
    return {
        str(row.get("id")): summarize_row(row)
        for row in attach_artifacts(rows, artifact)
        if isinstance(row, dict)
    }


def route_text(row: dict[str, Any] | None) -> str:
    if not row:
        return ""
    route = row.get("route")
    if route:
        return str(route)
    attempts = row.get("attempted_routes") or []
    return " ".join(str(item.get("route") or "") for item in attempts if isinstance(item, dict))


def classify_component(row: dict[str, Any] | None, verdict: str | None = None) -> str:
    text = route_text(row).lower()
    category = str((row or {}).get("category") or "")
    if "child_reference" in text or category == "child_reference_fallback":
        return "child_fallback_unknown_false" if verdict == "false" else "child_fallback_unknown_true"
    if "y_cert" in text or "cert" in text or "rowconst_certificate" in text:
        return "broad_certificate_pipeline"
    if "saturation" in text or "forward_saturation" in text:
        return "saturation_bodies"
    if "battery" in text:
        return "battery_bodies"
    if "standard_aux" in text or "y_aux" in text:
        return "standard_aux_superposition"
    if "superposition" in text or "goal_superposition" in text:
        return "superposition_bodies"
    if "cp_sat" in text:
        return "cp_sat_route"
    if "reference_ce" in text or "poly_ce" in text or "counterexample" in text:
        return "counterexample_family"
    if "model_finder" in text:
        return "model_finder_or_propagation"
    if "local_search" in text:
        return "local_search_route"
    if "llm:false_model_search" in text:
        return "llm_false_route_selection"
    if category == "llm_load_bearing":
        return "llm_orchestration"
    if verdict == "false":
        return "unknown_false_witness"
    return "unknown_true_proof"


def roi_score(component: str, rows: list[dict[str, Any]]) -> float:
    count = len(rows)
    solved = sum(1 for row in rows if row.get("reference", {}).get("solved"))
    base = count * 10 + solved * 4
    weights = {
        "broad_certificate_pipeline": 10,
        "counterexample_family": 9,
        "saturation_bodies": 7,
        "superposition_bodies": 6,
        "model_finder_or_propagation": 6,
        "cp_sat_route": 5,
        "battery_bodies": 4,
        "standard_aux_superposition": 3,
        "local_search_route": 3,
        "llm_orchestration": 2,
        "llm_false_route_selection": 2,
        "child_fallback_unknown_true": 5,
        "child_fallback_unknown_false": 5,
    }.get(component, 1)
    return base + weights


def analyze_gaps(
    problem_ids: list[str],
    x_summary: dict[str, dict[str, Any]],
    ref_summary: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    gaps: list[dict[str, Any]] = []
    clean_solver_only: list[dict[str, Any]] = []
    both_failed: list[dict[str, Any]] = []
    both_solved: list[dict[str, Any]] = []

    for pid in problem_ids:
        x = x_summary.get(pid, {"id": pid, "solved": False})
        ref = ref_summary.get(pid, {"id": pid, "solved": False})
        if ref.get("solved") and not x.get("solved"):
            component = classify_component(ref, ref.get("verdict"))
            gaps.append({
                "id": pid,
                "component": component,
                "verdict": ref.get("verdict"),
                "clean_solver": x,
                "reference": ref,
            })
        elif x.get("solved") and not ref.get("solved"):
            clean_solver_only.append({"id": pid, "clean_solver": x, "reference": ref})
        elif x.get("solved") and ref.get("solved"):
            both_solved.append({"id": pid, "clean_solver": x, "reference": ref})
        else:
            component = classify_component(x, None)
            both_failed.append({"id": pid, "component": component, "clean_solver": x, "reference": ref})

    grouped: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in gaps:
        grouped[row["component"]].append(row)
    ranked = [
        {
            "component": component,
            "gap_count": len(rows),
            "score": roi_score(component, rows),
            "problem_ids": [row["id"] for row in rows],
            "recommended_import": recommendation_for(component),
        }
        for component, rows in grouped.items()
    ]
    ranked.sort(key=lambda row: (-row["score"], row["component"]))
    return {
        "counts": {
            "reference_only_gaps": len(gaps),
            "clean_solver_only": len(clean_solver_only),
            "both_solved": len(both_solved),
            "both_failed": len(both_failed),
        },
        "gaps": gaps,
        "clean_solver_only": clean_solver_only,
        "both_failed": both_failed,
        "both_solved": both_solved,
        "ranked_components": ranked,
        "component_counts": dict(Counter(row["component"] for row in gaps)),
    }


def recommendation_for(component: str) -> str:
    return {
        "broad_certificate_pipeline": "Decompose the smallest winning certificate family into a protocol tool with helper/final-close feedback.",
        "counterexample_family": "Promote the witness family to a named false_model_search route with H/G violation telemetry.",
        "saturation_bodies": "Expose richer saturation generated-equation state and proof-body candidates under a bounded tool.",
        "superposition_bodies": "Increase native goal_superposition coverage or subgoal use where attribution shows a child-only win.",
        "model_finder_or_propagation": "Port the missing propagation/search branch and preserve blocked-cell/partial-table feedback.",
        "cp_sat_route": "Tune exact finite-domain route scheduling/budget, not the whole solver.",
        "battery_bodies": "Import the specific battery layer through graph-first proof consumption.",
        "standard_aux_superposition": "Extend aux lemma set or consumption bridges rather than importing broad machinery.",
        "local_search_route": "Add/retune route continuation policy or seed family with attribution.",
        "child_fallback_unknown_true": "Rerun with reference mechanical component tracing or external reference mechanical attribution; likely cert/saturation/superposition.",
        "child_fallback_unknown_false": "Rerun with reference mechanical component tracing; likely counterexample family or model finder route.",
    }.get(component, "Inspect attribution/logs, then import the smallest responsible tool.")


def write_markdown(result: dict[str, Any], path: Path) -> None:
    lines = [
        "# Native Gap Miner Report",
        "",
        f"- Source problems: `{result['problems']}`",
        f"- Effective problems: `{result['effective_problems']}`",
        f"- Problems: `{result['problem_count']}`",
        f"- ID filters: `{', '.join(result['id_filters']) if result['id_filters'] else '-'}`",
        f"- Max problems: `{result['max_problems'] if result['max_problems'] is not None else '-'}`",
        f"- clean solver solved: `{result['clean_solver_solved']}`",
        f"- Reference solved: `{result['reference_solved']}`",
        f"- Reference-only gaps: `{result['analysis']['counts']['reference_only_gaps']}`",
        f"- Clean-solver-only rows: `{result['analysis']['counts']['clean_solver_only']}`",
        f"- Both failed: `{result['analysis']['counts']['both_failed']}`",
        "",
        "## Ranked Native Import Candidates",
        "",
        "| Rank | Component | Gaps | Score | Problems | Recommended import |",
        "|---:|---|---:|---:|---|---|",
    ]
    ranked = result["analysis"]["ranked_components"]
    if ranked:
        for idx, row in enumerate(ranked, start=1):
            lines.append(
                f"| {idx} | `{row['component']}` | {row['gap_count']} | "
                f"{row['score']:.1f} | `{', '.join(row['problem_ids'])}` | "
                f"{row['recommended_import']} |"
            )
    else:
        lines.append("| - | - | 0 | 0 | - | No reference-only gaps in this corpus. Expand the corpus or use an external reference mechanical solver. |")
    if result["analysis"]["both_failed"]:
        lines.extend(["", "## Both Failed / Frontier Rows", ""])
        for row in result["analysis"]["both_failed"][:20]:
            lines.append(f"- `{row['id']}`: likely `{row['component']}` or new frontier; inspect clean solver failed routes.")
    if result["analysis"]["clean_solver_only"]:
        lines.extend(["", "## Clean-solver Only Wins", ""])
        for row in result["analysis"]["clean_solver_only"][:20]:
            lines.append(f"- `{row['id']}`")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--problems", type=Path, default=ROOT / ".artifacts" / "expected_win.jsonl")
    parser.add_argument("--config", type=Path, default=ROOT / ".artifacts" / "openrouter_fast_config.json")
    parser.add_argument("--solver", type=Path, default=ROOT / "baby_solver.py")
    parser.add_argument("--reference-submission", type=Path, default=None)
    parser.add_argument("--reference-solver", type=Path, default=None)
    parser.add_argument("--work-dir", type=Path, default=ROOT / ".artifacts" / "native_gap_miner")
    parser.add_argument("--output-json", type=Path, default=ROOT / ".artifacts" / "native_gap_miner_report.json")
    parser.add_argument("--output-md", type=Path, default=ROOT / ".artifacts" / "native_gap_miner_report.md")
    parser.add_argument("--timeout", type=float, default=3600.0)
    parser.add_argument(
        "--id",
        dest="ids",
        action="append",
        default=[],
        help="Problem id to include; may be repeated or comma-separated.",
    )
    parser.add_argument("--max-problems", type=int, default=None, help="Limit rows after id filtering.")
    args = parser.parse_args()

    args.work_dir.mkdir(parents=True, exist_ok=True)
    stamp = time.strftime("%Y%m%d_%H%M%S")
    id_filters = parse_id_filters(args.ids)
    effective_problems = prepare_effective_problems(
        args.problems,
        args.work_dir,
        ids=id_filters,
        max_problems=args.max_problems,
    )
    x_dir = prepare_submission_from_solver(args.solver, args.work_dir / "clean_solver_submission", disable_child_fallback=True)
    if args.reference_submission:
        ref_dir = prepare_submission_from_dir(args.reference_submission, args.work_dir / "reference_submission")
        ref_label = str(args.reference_submission)
    elif args.reference_solver:
        ref_dir = prepare_submission_from_solver(args.reference_solver, args.work_dir / "reference_submission", disable_child_fallback=False)
        ref_label = str(args.reference_solver)
    else:
        ref_dir = prepare_submission_from_solver(args.solver, args.work_dir / "reference_submission", disable_child_fallback=False)
        ref_label = f"{args.solver} (standalone control)"

    x_output = args.work_dir / f"clean_solver_{stamp}.json"
    ref_output = args.work_dir / f"reference_{stamp}.json"
    x_rows = run_pipeline(x_dir, effective_problems, args.config, x_output, timeout=args.timeout)
    ref_rows = run_pipeline(ref_dir, effective_problems, args.config, ref_output, timeout=args.timeout)

    problem_ids = read_problem_ids(effective_problems)
    x_summary = summary_by_id(x_rows, x_output)
    ref_summary = summary_by_id(ref_rows, ref_output)
    analysis = analyze_gaps(problem_ids, x_summary, ref_summary)
    result = {
        "generated_at": stamp,
        "problems": str(args.problems),
        "effective_problems": str(effective_problems),
        "id_filters": sorted(id_filters),
        "max_problems": args.max_problems,
        "problem_count": len(problem_ids),
        "config": str(args.config),
        "clean_solver_submission": str(x_dir),
        "reference": ref_label,
        "reference_submission": str(ref_dir),
        "clean_solver_output": str(x_output),
        "reference_output": str(ref_output),
        "clean_solver_solved": sum(1 for row in x_rows if row.get("solved")),
        "reference_solved": sum(1 for row in ref_rows if row.get("solved")),
        "analysis": analysis,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(result, args.output_md)
    print(json.dumps({
        "output_json": str(args.output_json),
        "output_md": str(args.output_md),
        "clean_solver_solved": result["clean_solver_solved"],
        "reference_solved": result["reference_solved"],
        "reference_only_gaps": analysis["counts"]["reference_only_gaps"],
        "ranked_components": analysis["ranked_components"][:5],
    }, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
