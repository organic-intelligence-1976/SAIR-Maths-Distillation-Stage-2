#!/usr/bin/env python3
"""Assemble and Lean-check a structured infinite-countermodel plan."""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from research_system.curriculum import reference_cases  # noqa: E402
from research_system.executor import MechanicalExecutor  # noqa: E402
from research_system.infinite_models import assemble_infinite_model_plan  # noqa: E402
from research_system.verifier import OfficialLeanVerifier  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--plan",
        type=Path,
        default=ROOT / "data" / "semantics" / "austin_3994_3588_infinite_model_plan.json",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / ".artifacts" / "structured_infinite_model_probe.json",
    )
    parser.add_argument("--timeout", type=int, default=90)
    args = parser.parse_args()

    plan = json.loads(args.plan.read_text(encoding="utf-8"))
    code, assembly_state = assemble_infinite_model_plan(plan)
    case = reference_cases()["reference_infinite_false"]
    started = time.monotonic()
    execution = MechanicalExecutor().execute(
        case.problem,
        plan,
        semantics=None,
    )
    verification = OfficialLeanVerifier(timeout_seconds=args.timeout).verify(
        case.problem,
        execution,
        profile="research",
    )
    output = {
        "schema_version": 1,
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "case_id": case.case_id,
        "plan": str(args.plan),
        "assembly_state": assembly_state,
        "execution": execution.to_mapping(),
        "verification": verification.to_mapping(),
        "assembled_code_bytes": len(code.encode("utf-8")) if code else None,
        "seconds": round(time.monotonic() - started, 3),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(output, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({
        "output": str(args.output),
        "assembly_status": assembly_state.get("status"),
        "verification_status": verification.status,
        "accepted": verification.accepted,
        "assembled_code_bytes": output["assembled_code_bytes"],
        "seconds": output["seconds"],
    }, ensure_ascii=False))
    return 0 if verification.accepted else 1


if __name__ == "__main__":
    raise SystemExit(main())
