#!/usr/bin/env python3
"""Test live System-2 repair of a mechanically failed finite-model family."""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from research_system.curriculum import CurriculumCase, load_problem  # noqa: E402
from research_system.executor import MechanicalExecutor  # noqa: E402
from research_system.orchestrator import ResearchEpisodeRunner  # noqa: E402
from research_system.planner import (  # noqa: E402
    FeedbackRepairPlanner,
    OpenAICompatiblePlanner,
    Planner,
)
from research_system.semantics import SemanticService  # noqa: E402
from research_system.verifier import OfficialLeanVerifier  # noqa: E402


class SeededFeedbackPlanner:
    """Use one controlled family miss, then let the live planner repair it."""

    name = "seeded_finite_model_feedback"

    def __init__(
        self,
        planner: Planner,
        *,
        control_size: int,
        fiber_size: int,
        budget: float,
    ):
        self.planner = planner
        self.control_size = control_size
        self.fiber_size = fiber_size
        self.budget = budget
        self.round = 0
        self.traces: list[dict[str, Any]] = []

    @property
    def last_trace(self) -> dict[str, Any] | None:
        return self.traces[-1] if self.traces else None

    def next_action(self, context: dict[str, Any]) -> dict[str, Any] | None:
        self.round += 1
        if self.round == 1:
            action = {
                "kind": "skew_model_search",
                "control_size": self.control_size,
                "fiber_size": self.fiber_size,
                "fiber_library": "affine",
                "require_quotient_goal": True,
                "budget": self.budget,
            }
            self.traces.append({"status": "scripted_seed", "action": action})
            return action
        focused_context = dict(context)
        focused_context["teacher_search"] = {
            "focus": "finite_symbolic",
            "proposal_slot": self.round - 1,
            "directive": (
                "Return kind=bundle_model_search or kind=skew_model_search "
                "only. If the latest observation has "
                "mechanical_status=family_infeasible and "
                "suggested_next_actions, return the first suggested action "
                "exactly."
            ),
        }
        action = self.planner.next_action(focused_context)
        self.traces.append(dict(self.planner.last_trace or {}))
        return action


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--problem-id", default="hard2_0125")
    parser.add_argument(
        "--llm-config",
        type=Path,
        default=ROOT / "configs" / "openrouter_gpt_oss_120b.example.json",
    )
    parser.add_argument("--control-size", type=int, default=2)
    parser.add_argument("--fiber-size", type=int, default=2)
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--mechanical-budget", type=float, default=15.0)
    parser.add_argument("--llm-timeout", type=float, default=150.0)
    parser.add_argument("--judge-timeout", type=int, default=90)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / ".artifacts" / "bundle_feedback_probe.json",
    )
    args = parser.parse_args()

    config = json.loads(args.llm_config.read_text(encoding="utf-8"))
    live = OpenAICompatiblePlanner(config, timeout=args.llm_timeout)
    guided = FeedbackRepairPlanner(live, max_corrections=1)
    planner = SeededFeedbackPlanner(
        guided,
        control_size=args.control_size,
        fiber_size=args.fiber_size,
        budget=args.mechanical_budget,
    )
    problem = load_problem(args.problem_id)
    if problem.answer is not False:
        parser.error(f"{args.problem_id} is not labeled false")
    case = CurriculumCase(
        case_id=f"bundle_feedback_{args.problem_id}",
        problem=problem,
        actions=(),
        expected_verdict="false",
        max_rounds=max(2, args.rounds),
        tags=("finite_symbolic", "feedback_chain"),
    )
    runner = ResearchEpisodeRunner(
        semantics=SemanticService(
            ROOT / "data" / "semantics" / "austin_implications.json"
        ),
        executor=MechanicalExecutor(),
        verifier=OfficialLeanVerifier(timeout_seconds=args.judge_timeout),
    )
    started = time.monotonic()
    episode, _artifact = runner.run(
        case,
        planner,
        persist=False,
        distill=False,
    )
    output = {
        "schema_version": 1,
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "problem_id": args.problem_id,
        "episode": episode.to_mapping(),
        "planner_traces": planner.traces,
        "seconds": round(time.monotonic() - started, 3),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(output, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({
        "output": str(args.output),
        "accepted": episode.accepted,
        "verdict": (episode.verification or {}).get("verdict"),
        "attempts": len(episode.attempts),
        "seconds": output["seconds"],
    }, ensure_ascii=False))
    return 0 if episode.accepted else 1


if __name__ == "__main__":
    raise SystemExit(main())
