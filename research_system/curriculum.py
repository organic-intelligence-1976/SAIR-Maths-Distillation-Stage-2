"""Reference curriculum cases spanning true, finite-false, and infinite lanes."""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from .protocol import ProblemSpec


ROOT = Path(__file__).resolve().parents[1]
PROBLEM_DIR = ROOT / "official-stage2" / "examples" / "problems"


def load_problem(problem_id: str) -> ProblemSpec:
    for path in sorted(PROBLEM_DIR.glob("*")):
        if not path.is_file() or path.suffix not in {".json", ".jsonl"}:
            continue
        try:
            text = path.read_text(encoding="utf-8").strip()
            rows = json.loads(text) if text.startswith("[") else [
                json.loads(line) for line in text.splitlines() if line.strip()
            ]
        except Exception:
            continue
        if not isinstance(rows, list):
            continue
        for row in rows:
            if isinstance(row, dict) and row.get("id") == problem_id:
                return ProblemSpec.from_mapping(row)
    raise KeyError(f"problem not found: {problem_id}")


@dataclass(frozen=True)
class CurriculumCase:
    case_id: str
    problem: ProblemSpec
    actions: tuple[dict[str, Any], ...]
    capability_mask: dict[str, Any] = field(default_factory=lambda: {"disabled": []})
    negative_control_mask: dict[str, Any] = field(default_factory=lambda: {"disabled": []})
    full_action: dict[str, Any] | None = None
    verification_profile: str = "competition"
    split_label: str = "development"
    expected_verdict: str = "true"
    max_rounds: int = 4
    tags: tuple[str, ...] = ()


def reference_cases() -> dict[str, CurriculumCase]:
    right_square = CurriculumCase(
        case_id="reference_true_right_square",
        problem=load_problem("hard2_0107"),
        actions=(
            {
                "kind": "tool_call",
                "tool": "lemma_chain",
                "target": "goal",
                "lemmas": [
                    {"name": "square_absorb", "equation": "u ◇ (v ◇ v) = v"},
                ],
            },
            {
                "kind": "midpoint",
                "lemma": "a ◇ b = b ◇ b",
                "why": "the blackboard retains the already verified square_absorb node",
            },
        ),
        capability_mask={"disabled": ["tool:right_square_chain"]},
        negative_control_mask={
            "disabled": ["tool:right_square_chain", "primitive:generic_midpoint_prover"],
        },
        full_action={"kind": "tool_call", "tool": "right_square_chain", "target": "goal"},
        expected_verdict="true",
        tags=("true", "partial_progress", "capability_dropout", "blackboard"),
    )
    finite_false = CurriculumCase(
        case_id="reference_finite_false",
        problem=load_problem("hard1_0006"),
        actions=(
            {
                "kind": "false_table",
                "counterexample_table": [[0, 0], [1, 1]],
            },
        ),
        expected_verdict="false",
        max_rounds=1,
        tags=("false", "finite_model", "direct_artifact"),
    )
    infinite_problem = ProblemSpec(
        id="reference_austin_3994_3588",
        eq1_id=3994,
        eq2_id=3588,
        equation1="x ◇ y = (z ◇ (x ◇ y)) ◇ z",
        equation2="x ◇ y = z ◇ ((x ◇ y) ◇ z)",
        answer=False,
    )
    infinite_code = (ROOT / "data" / "semantics" / "austin_3994_3588_infinite_model.lean").read_text(encoding="utf-8")
    infinite_false = CurriculumCase(
        case_id="reference_infinite_false",
        problem=infinite_problem,
        actions=({"kind": "infinite_model", "code": infinite_code},),
        verification_profile="research",
        expected_verdict="false",
        max_rounds=1,
        tags=("false", "infinite_model", "research_only", "austin"),
    )
    return {
        case.case_id: case
        for case in (right_square, finite_false, infinite_false)
    }

