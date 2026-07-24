"""Paired curriculum evaluation over the modular episode runtime."""

from __future__ import annotations

from dataclasses import replace
from typing import Any

from .curriculum import CurriculumCase
from .orchestrator import ResearchEpisodeRunner
from .planner import ScriptedPlanner


class CurriculumEvaluator:
    def __init__(self, runner: ResearchEpisodeRunner):
        self.runner = runner

    def _run(self, case: CurriculumCase, label: str) -> dict[str, Any]:
        episode, artifact = self.runner.run(
            case,
            ScriptedPlanner(list(case.actions), name=f"scripted:{label}"),
        )
        return {
            "episode": episode.to_mapping(),
            "artifact": artifact.to_mapping() if artifact else None,
        }

    def evaluate(self, case: CurriculumCase) -> dict[str, Any]:
        curriculum = self._run(case, "curriculum")
        full = None
        negative = None
        if case.full_action is not None:
            full_case = replace(
                case,
                case_id=f"{case.case_id}__full",
                actions=(case.full_action,),
                capability_mask={"disabled": []},
                max_rounds=1,
            )
            full = self._run(full_case, "full")
            negative_case = replace(
                case,
                case_id=f"{case.case_id}__negative",
                capability_mask=case.negative_control_mask,
            )
            negative = self._run(negative_case, "negative")
        checks = {
            "curriculum_accepted": bool(curriculum["episode"]["accepted"]),
            "expected_verdict_matched": (
                (curriculum["episode"].get("verification") or {}).get("verdict")
                == case.expected_verdict
            ),
        }
        if full is not None and negative is not None:
            checks.update({
                "full_baseline_accepted": bool(full["episode"]["accepted"]),
                "negative_control_failed": not bool(negative["episode"]["accepted"]),
            })
        return {
            "case_id": case.case_id,
            "eligible": all(checks.values()),
            "checks": checks,
            "curriculum": curriculum,
            "full": full,
            "negative": negative,
        }

