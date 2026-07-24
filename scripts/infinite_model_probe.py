#!/usr/bin/env python3
"""Verify the research infinite-model artifact boundary on a closed Austin pair."""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "official-stage2"))

import baby_solver as solver  # noqa: E402
from judge.verify import JudgeConfig, _resolve_config, verify_answer  # type: ignore  # noqa: E402
from pipeline.proxy import DEFAULT_PROOF_POLICY  # type: ignore  # noqa: E402

FIXTURE = {
    "id": "research_austin_3994_3588",
    "eq1_id": 3994,
    "eq2_id": 3588,
    "equation1": "x ◇ y = (z ◇ (x ◇ y)) ◇ z",
    "equation2": "x ◇ y = z ◇ ((x ◇ y) ◇ z)",
}


def judge_config(timeout: int) -> JudgeConfig:
    base = _resolve_config(None)
    return JudgeConfig(
        lean_bin=base.lean_bin,
        lake_bin=base.lake_bin,
        artifact_dir=ROOT / ".artifacts" / "infinite_model_judge",
        lean_timeout_seconds=timeout,
        max_code_length=base.max_code_length,
        max_false_cert_bytes=base.max_false_cert_bytes,
    )


def compact_result(result: dict[str, Any], seconds: float) -> dict[str, Any]:
    return {
        "status": result.get("status"),
        "error_code": result.get("error_code"),
        "message": result.get("message"),
        "axioms": result.get("axioms"),
        "direct_declaration_count": len(result.get("direct_declarations") or []),
        "seconds": round(seconds, 3),
    }


def verify_profile(code: str, profile: str, timeout: int) -> dict[str, Any]:
    if profile == "research":
        proof_policy = {"allowed_axioms": ["propext", "Quot.sound", "Classical.choice"]}
    elif profile == "competition":
        proof_policy = DEFAULT_PROOF_POLICY
    else:
        raise ValueError(f"unknown profile: {profile}")
    problem = {**FIXTURE, "id": f"{FIXTURE['id']}_{profile}", "proof_policy": proof_policy}
    started = time.monotonic()
    result = verify_answer(
        problem,
        json.dumps({"verdict": "false", "code": code}),
        config=judge_config(timeout),
    )
    return compact_result(result, time.monotonic() - started)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--artifact",
        type=Path,
        default=ROOT / "data" / "semantics" / "austin_3994_3588_infinite_model.lean",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / ".artifacts" / "infinite_model_probe.json",
    )
    parser.add_argument("--timeout", type=int, default=60)
    args = parser.parse_args()

    code = args.artifact.read_text(encoding="utf-8")
    normalized, adapter_state = solver.normalize_llm_action({
        "kind": "infinite_model",
        "code": code,
    })
    validated_code, envelope_state = solver.validate_infinite_model_payload(normalized or {})
    if validated_code is None:
        raise ValueError(envelope_state)
    research = verify_profile(validated_code, "research", args.timeout)
    competition = verify_profile(validated_code, "competition", args.timeout)
    output = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "fixture": FIXTURE,
        "source": {
            "repository": "https://github.com/teorth/equational_theories",
            "commit": "df8184f8ae59c71d6f5463b71682d871823a779c",
            "theorem": "InfModel.Equation3994_not_implies_Equation3588",
        },
        "artifact": str(args.artifact),
        "artifact_bytes": len(code.encode("utf-8")),
        "adapter_state": adapter_state,
        "envelope_state": envelope_state,
        "research_policy": research,
        "competition_policy": competition,
        "interpretation": (
            "The Type-level countermodel is accepted by Lean under the research declaration policy. "
            "Any competition-policy rejection is a deployability constraint, not a mathematical refutation."
        ),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({
        "output": str(args.output),
        "research_status": research["status"],
        "competition_status": competition["status"],
        "artifact_bytes": output["artifact_bytes"],
    }))
    return 0 if research["status"] == "accepted" else 1


if __name__ == "__main__":
    raise SystemExit(main())
