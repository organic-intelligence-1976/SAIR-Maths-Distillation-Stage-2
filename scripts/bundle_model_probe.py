#!/usr/bin/env python3
"""Probe non-uniform quotient bundles with sparse patched fiber maps."""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import baby_solver  # noqa: E402
from research_system.curriculum import load_problem  # noqa: E402
from research_system.finite_models import (  # noqa: E402
    BundleModelConfig,
    bundle_counterexample_search,
)
from research_system.protocol import ExecutionResult  # noqa: E402
from research_system.verifier import OfficialLeanVerifier  # noqa: E402


def parse_fiber_sizes(value: str) -> tuple[int, ...]:
    try:
        sizes = tuple(int(part) for part in value.replace("×", ",").split(","))
    except ValueError as exc:
        raise argparse.ArgumentTypeError("fiber sizes must be integers") from exc
    if len(sizes) < 2 or any(size < 1 for size in sizes) or sum(sizes) > 40:
        raise argparse.ArgumentTypeError(
            "require at least two positive fiber sizes with total at most 40"
        )
    return sizes


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--problem-id", action="append")
    parser.add_argument(
        "--fiber-sizes",
        action="append",
        type=parse_fiber_sizes,
        help="Comma-separated non-uniform fiber sizes, such as 4,2",
    )
    parser.add_argument("--max-patches", action="append", type=int)
    parser.add_argument("--budget", type=float, default=30.0)
    parser.add_argument("--max-iterations", type=int, default=160)
    parser.add_argument("--violation-batch", type=int, default=12)
    parser.add_argument("--judge-timeout", type=int, default=90)
    parser.add_argument("--skip-judge", action="store_true")
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / ".artifacts" / "bundle_model_probe.json",
    )
    args = parser.parse_args()

    problem_ids = args.problem_id or ["hard2_0125"]
    fiber_shapes = args.fiber_sizes or [(4, 2)]
    patch_limits = args.max_patches or [6]
    verifier = OfficialLeanVerifier(timeout_seconds=args.judge_timeout)
    started = time.monotonic()
    rows = []

    for problem_id in problem_ids:
        problem = load_problem(problem_id)
        if problem.answer is not False:
            parser.error(f"{problem_id} is not labeled false")
        h_eq = baby_solver.parse_equation(problem.equation1)
        g_eq = baby_solver.parse_equation(problem.equation2)
        for fibers in fiber_shapes:
            for max_patches in patch_limits:
                config = BundleModelConfig(
                    fiber_sizes=fibers,
                    max_patches=max_patches,
                    time_budget=args.budget,
                    max_iterations=args.max_iterations,
                    violation_batch=args.violation_batch,
                ).normalized()
                status, table, state = bundle_counterexample_search(
                    h_eq,
                    g_eq,
                    config,
                )
                mechanically_valid = bool(
                    table is not None
                    and baby_solver.is_counterexample(h_eq, g_eq, table)
                )
                verification = None
                if mechanically_valid and not args.skip_judge:
                    verification = verifier.verify(
                        problem,
                        ExecutionResult(
                            status="candidate_ready",
                            finite_table=table,
                            state=state,
                        ),
                    ).to_mapping()
                rows.append({
                    "problem_id": problem_id,
                    "equation1": problem.equation1,
                    "equation2": problem.equation2,
                    "fiber_sizes": list(fibers),
                    "max_patches": max_patches,
                    "status": status,
                    "mechanically_valid": mechanically_valid,
                    "state": state,
                    "verification": verification,
                    "table": table,
                })

    output = {
        "schema_version": 1,
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "rows": rows,
        "seconds": round(time.monotonic() - started, 3),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(output, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({
        "output": str(args.output),
        "rows": len(rows),
        "found": sum(1 for row in rows if row["mechanically_valid"]),
        "judge_accepted": sum(
            1
            for row in rows
            if isinstance(row["verification"], dict)
            and row["verification"].get("accepted")
        ),
        "seconds": output["seconds"],
    }, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
