#!/usr/bin/env python3
"""Probe compact skew-product countermodels on official false implications."""

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
    SkewProductConfig,
    skew_product_counterexample_search,
)
from research_system.protocol import ExecutionResult  # noqa: E402
from research_system.verifier import OfficialLeanVerifier  # noqa: E402


def parse_factor(value: str) -> tuple[int, int]:
    normalized = value.lower().replace("×", "x")
    parts = normalized.split("x")
    if len(parts) != 2:
        raise argparse.ArgumentTypeError("factor must look like 2x3")
    try:
        control, fiber = (int(part) for part in parts)
    except ValueError as exc:
        raise argparse.ArgumentTypeError("factor sizes must be integers") from exc
    if control < 1 or fiber < 2 or control * fiber > 40:
        raise argparse.ArgumentTypeError("require control >= 1, fiber >= 2, product <= 40")
    return control, fiber


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--problem-id",
        action="append",
        help="Official false problem ID; repeat as needed",
    )
    parser.add_argument(
        "--factor",
        action="append",
        type=parse_factor,
        help="Control-by-fiber factorization such as 2x3",
    )
    parser.add_argument("--budget", type=float, default=20.0)
    parser.add_argument("--max-iterations", type=int, default=96)
    parser.add_argument("--violation-batch", type=int, default=12)
    parser.add_argument(
        "--fiber-library",
        choices=("affine", "affine_order"),
        default="affine",
    )
    parser.add_argument(
        "--allow-quotient-counterexample",
        action="store_true",
        help="Do not require the smaller quotient to satisfy G",
    )
    parser.add_argument("--judge-timeout", type=int, default=90)
    parser.add_argument(
        "--skip-judge",
        action="store_true",
        help="Mechanically check the table but do not invoke the official Lean judge",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / ".artifacts" / "skew_model_probe.json",
    )
    args = parser.parse_args()

    problem_ids = args.problem_id or ["hard2_0125", "hard2_0093"]
    factors = args.factor or [(2, 2), (2, 3), (3, 2)]
    verifier = OfficialLeanVerifier(timeout_seconds=args.judge_timeout)
    started = time.monotonic()
    rows = []

    for problem_id in problem_ids:
        problem = load_problem(problem_id)
        if problem.answer is not False:
            parser.error(f"{problem_id} is not labeled false")
        h_eq = baby_solver.parse_equation(problem.equation1)
        g_eq = baby_solver.parse_equation(problem.equation2)
        invariant_report = baby_solver.symbolic_invariant_report(h_eq, g_eq)
        for control, fiber in factors:
            config = SkewProductConfig(
                control_size=control,
                fiber_size=fiber,
                fiber_library=args.fiber_library,
                require_quotient_goal=not args.allow_quotient_counterexample,
                time_budget=args.budget,
                max_iterations=args.max_iterations,
                violation_batch=args.violation_batch,
            ).normalized()
            status, table, state = skew_product_counterexample_search(
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
                execution = ExecutionResult(
                    status="candidate_ready",
                    finite_table=table,
                    state=state,
                )
                verification = verifier.verify(problem, execution).to_mapping()
            rows.append({
                "problem_id": problem_id,
                "equation1": problem.equation1,
                "equation2": problem.equation2,
                "factorization": [control, fiber],
                "status": status,
                "mechanically_valid": mechanically_valid,
                "state": state,
                "verification": verification,
                "simple_invariant_separators": [
                    row.get("family")
                    for row in invariant_report
                    if row.get("separates_goal")
                ],
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
