#!/usr/bin/env python3
"""Exercise a compiled solver.py through the official proxy and Lean judge."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OFFICIAL = ROOT / "official-stage2"
sys.path.insert(0, str(OFFICIAL))

from pipeline.proxy import load_config, run_solver  # type: ignore  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--submission-dir",
        type=Path,
        default=ROOT / ".artifacts" / "compiled_submission" / "submission",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / ".artifacts" / "compiled_submission" / "protocol_smoke.json",
    )
    parser.add_argument("--solver-timeout", type=int, default=90)
    parser.add_argument("--judge-timeout", type=int, default=45)
    args = parser.parse_args()

    config = load_config(str(OFFICIAL / "pipeline" / "config.json"))
    config["solver"]["timeout_seconds"] = args.solver_timeout
    config["judge"]["lean_timeout_seconds"] = args.judge_timeout
    problem = {
        "id": "compiled_protocol_smoke",
        "eq1_id": 999001,
        "eq2_id": 999002,
        "equation1": "x ◇ y = x ◇ y",
        "equation2": "x ◇ y = x ◇ y",
        "answer": True,
    }
    result = run_solver(args.submission_dir, problem, config)
    output = {
        "submission_dir": str(args.submission_dir),
        "problem": problem,
        "result": result,
        "checks": {
            "solved": bool(result.get("solved")),
            "true_verdict": result.get("verdict") == "true",
            "no_llm_calls": result.get("llm_calls") == 0,
            "one_judge_call": result.get("judge_calls") == 1,
        },
    }
    output["passed"] = all(output["checks"].values())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({
        "output": str(args.output),
        "passed": output["passed"],
        "checks": output["checks"],
    }))
    return 0 if output["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

