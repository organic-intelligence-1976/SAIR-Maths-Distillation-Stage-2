"""Official Lean verification boundary for true, finite-false, and infinite artifacts."""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path
from typing import Any

import baby_solver

from .protocol import ExecutionResult, ProblemSpec, VerificationRecord


ROOT = Path(__file__).resolve().parents[1]
OFFICIAL = ROOT / "official-stage2"
if str(OFFICIAL) not in sys.path:
    sys.path.insert(0, str(OFFICIAL))

from judge.verify import JudgeConfig, _resolve_config, verify_answer  # type: ignore  # noqa: E402
from pipeline.proxy import DEFAULT_PROOF_POLICY  # type: ignore  # noqa: E402


class OfficialLeanVerifier:
    def __init__(self, *, timeout_seconds: int = 30, artifact_dir: Path | None = None):
        self.timeout_seconds = timeout_seconds
        self.artifact_dir = artifact_dir or ROOT / ".artifacts" / "research_system_judge"

    def _config(self) -> JudgeConfig:
        base = _resolve_config(None)
        return JudgeConfig(
            lean_bin=base.lean_bin,
            lake_bin=base.lake_bin,
            artifact_dir=self.artifact_dir,
            lean_timeout_seconds=max(1, int(self.timeout_seconds)),
            max_code_length=base.max_code_length,
            max_false_cert_bytes=base.max_false_cert_bytes,
        )

    @staticmethod
    def _problem(problem: ProblemSpec, profile: str) -> dict[str, Any]:
        out = problem.to_mapping()
        if profile == "research":
            out["proof_policy"] = {
                "allowed_axioms": ["propext", "Quot.sound", "Classical.choice"],
            }
        elif problem.proof_policy:
            out["proof_policy"] = problem.proof_policy
        else:
            out["proof_policy"] = DEFAULT_PROOF_POLICY
        return out

    def verify(
        self,
        problem: ProblemSpec,
        execution: ExecutionResult,
        *,
        profile: str = "competition",
    ) -> VerificationRecord:
        started = time.monotonic()
        if execution.body:
            verdict = "true"
            code = baby_solver.make_true_code(execution.body)
        elif execution.finite_table is not None:
            verdict = "false"
            code = baby_solver.make_false_code(len(execution.finite_table), execution.finite_table)
        elif execution.infinite_code:
            verdict = "false"
            code = execution.infinite_code
        else:
            return VerificationRecord(
                status="no_candidate",
                accepted=False,
                verdict="unknown",
                profile=profile,
                message="mechanical executor did not produce a verifiable artifact",
            )
        try:
            result = verify_answer(
                self._problem(problem, profile),
                json.dumps({"verdict": verdict, "code": code}),
                config=self._config(),
            )
            status = str(result.get("status") or "unknown")
            return VerificationRecord(
                status=status,
                accepted=status == "accepted",
                verdict=verdict,
                profile=profile,
                message=result.get("message"),
                error_code=result.get("error_code"),
                seconds=time.monotonic() - started,
                details={
                    "axioms": result.get("axioms"),
                    "direct_declaration_count": len(result.get("direct_declarations") or []),
                    "stderr": str(result.get("stderr") or "")[:1600],
                },
            )
        except Exception as exc:
            return VerificationRecord(
                status="verifier_error",
                accepted=False,
                verdict=verdict,
                profile=profile,
                message=repr(exc),
                seconds=time.monotonic() - started,
            )

