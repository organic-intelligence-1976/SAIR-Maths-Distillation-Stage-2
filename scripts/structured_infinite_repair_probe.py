#!/usr/bin/env python3
"""Live repair of one rejected structured infinite-model component."""

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
from research_system.experience import ExperienceStore  # noqa: E402
from research_system.orchestrator import ResearchEpisodeRunner  # noqa: E402
from research_system.planner import (  # noqa: E402
    ContextAugmentingPlanner,
    OpenAICompatiblePlanner,
    ScriptedPlanner,
)
from research_system.semantics import SemanticService  # noqa: E402
from research_system.structure import problem_structure  # noqa: E402
from research_system.teacher import (  # noqa: E402
    TEACHER_STUDENT_VERSION,
    TeacherSearchConfig,
    TeacherStudentSearch,
)
from research_system.verifier import OfficialLeanVerifier  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--plan",
        type=Path,
        default=ROOT / "data" / "semantics" / "austin_3994_3588_infinite_model_plan.json",
    )
    parser.add_argument(
        "--llm-config",
        type=Path,
        default=ROOT / ".artifacts" / "team_y_suspected_top20_config.json",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / ".artifacts" / "structured_infinite_repair_live.json",
    )
    parser.add_argument(
        "--store",
        type=Path,
        default=ROOT / ".artifacts" / "research_system" / "structured_infinite_repair",
    )
    parser.add_argument("--llm-timeout", type=float, default=120.0)
    parser.add_argument("--judge-timeout", type=int, default=90)
    parser.add_argument("--beam-width", type=int, default=2)
    parser.add_argument("--proposals-per-branch", type=int, default=3)
    parser.add_argument("--max-depth", type=int, default=3)
    parser.add_argument("--proposal-workers", type=int, default=3)
    parser.add_argument(
        "--student-replay",
        action="store_true",
        help="Run ordinary-model no-lesson and with-lesson attribution controls",
    )
    parser.add_argument(
        "--replay-only-from",
        type=Path,
        help="Reuse a prior verified teacher report and run only student attribution",
    )
    args = parser.parse_args()

    if not args.plan.is_file():
        parser.error(f"plan does not exist: {args.plan}")
    if not args.llm_config.is_file():
        parser.error(f"LLM config does not exist: {args.llm_config}")
    plan = json.loads(args.plan.read_text(encoding="utf-8"))
    config = json.loads(args.llm_config.read_text(encoding="utf-8"))
    broken = dict(plan)
    broken["hypothesis_proof"] = str(plan["hypothesis_proof"]).replace(
        "Nat.xor_comm",
        "Nat.xor_comm_typo",
    )
    if broken["hypothesis_proof"] == plan["hypothesis_proof"]:
        parser.error("fixture mutation did not change the hypothesis proof")

    case = reference_cases()["reference_infinite_false"]
    store = ExperienceStore(args.store)
    runner = ResearchEpisodeRunner(
        semantics=SemanticService(ROOT / "data" / "semantics" / "austin_implications.json"),
        executor=MechanicalExecutor(),
        verifier=OfficialLeanVerifier(timeout_seconds=args.judge_timeout),
        store=store,
    )
    repair_config = TeacherSearchConfig(
        beam_width=args.beam_width,
        proposals_per_branch=args.proposals_per_branch,
        max_depth=args.max_depth,
        branch_rounds=1,
        student_rounds=2,
        focus="infinite_model",
        proposal_workers=args.proposal_workers,
    )

    def student_factory(lesson: dict | None):
        additions = {
            "teacher_search": {
                "mode": "ordinary_student_replay",
                "focus": "infinite_model",
                "directive": (
                    "This is an exact-problem replay control. If teacher_lesson has a "
                    "complete decisive infinite_model_plan, return that plan verbatim "
                    "on round 1, preserving model_name and every identifier reference. "
                    "Otherwise use the structured infinite-model action language. Do "
                    "not search finite tables."
                ),
            },
        }
        if lesson is not None:
            additions["teacher_lesson"] = lesson
        return ContextAugmentingPlanner(
            OpenAICompatiblePlanner(config, timeout=args.llm_timeout),
            additions,
            name=(
                "ordinary_infinite_student_with_lesson"
                if lesson is not None
                else "ordinary_infinite_student_no_lesson"
            ),
        )

    if args.replay_only_from is not None:
        if not args.replay_only_from.is_file():
            parser.error(f"replay report does not exist: {args.replay_only_from}")
        source_payload = json.loads(args.replay_only_from.read_text(encoding="utf-8"))
        source_report = (
            source_payload.get("repair")
            if isinstance(source_payload.get("repair"), dict)
            else source_payload
        )
        minimized = source_report.get("minimization")
        actions = minimized.get("actions") if isinstance(minimized, dict) else None
        if not isinstance(actions, list) or not actions:
            parser.error("replay report has no minimized verified actions")
        lesson = {
            "version": TEACHER_STUDENT_VERSION,
            "kind": "verified_teacher_trajectory",
            "problem_structure": problem_structure(case.problem),
            "expected_verdict": case.expected_verdict,
            "decisive_actions": actions,
            "instruction": (
                "Exact-problem attribution replay: reproduce the complete decisive "
                "action verbatim before attempting any repair."
            ),
        }
        replay_search = TeacherStudentSearch(
            runner,
            ScriptedPlanner([], name="student_replay_only"),
            config=repair_config,
            student_planner_factory=student_factory,
        )
        started = time.monotonic()
        replay = replay_search.replay_student_lesson(case, lesson)
        output = {
            "schema_version": 1,
            "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "case_id": case.case_id,
            "source_report": str(args.replay_only_from),
            "lesson": lesson,
            "student": {
                "no_lesson": (
                    replay["no_lesson"].to_mapping()
                    if replay["no_lesson"] is not None
                    else None
                ),
                "with_lesson": (
                    replay["with_lesson"].to_mapping()
                    if replay["with_lesson"] is not None
                    else None
                ),
                "no_lesson_accepted": replay["no_lesson_accepted"],
                "student_accepted": replay["student_accepted"],
                "load_bearing": replay["load_bearing"],
            },
            "seconds": round(time.monotonic() - started, 3),
            "experience_store": store.summary(),
        }
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(
            json.dumps(output, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
        print(json.dumps({
            "output": str(args.output),
            "no_lesson_accepted": replay["no_lesson_accepted"],
            "student_accepted": replay["student_accepted"],
            "load_bearing": replay["load_bearing"],
            "seconds": output["seconds"],
        }, ensure_ascii=False))
        return 0

    seed_search = TeacherStudentSearch(
        runner,
        ScriptedPlanner([broken], name="broken_structured_seed"),
        config=TeacherSearchConfig(
            beam_width=1,
            proposals_per_branch=1,
            max_depth=1,
            branch_rounds=1,
            student_rounds=2,
            focus="infinite_model",
        ),
    )
    started = time.monotonic()
    seed_report = seed_search.run(case)
    if seed_report.get("outcome") != "teacher_unsolved":
        parser.error(f"broken seed unexpectedly did not fail: {seed_report.get('outcome')}")

    repair_search = TeacherStudentSearch(
        runner,
        OpenAICompatiblePlanner(config, timeout=args.llm_timeout),
        config=repair_config,
        teacher_planner_factory=lambda: OpenAICompatiblePlanner(
            config,
            timeout=args.llm_timeout,
        ),
        student_planner_factory=student_factory if args.student_replay else None,
    )
    repair_report = repair_search.run(case, resume_from=seed_report)
    output = {
        "schema_version": 1,
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "case_id": case.case_id,
        "fixture_plan": str(args.plan),
        "injected_fault": {
            "part": "hypothesis_proof",
            "from": "Nat.xor_comm",
            "to": "Nat.xor_comm_typo",
        },
        "seed": seed_report,
        "repair": repair_report,
        "seconds": round(time.monotonic() - started, 3),
        "experience_store": store.summary(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(output, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({
        "output": str(args.output),
        "seed_outcome": seed_report.get("outcome"),
        "repair_outcome": repair_report.get("outcome"),
        "teacher_actions": repair_report.get("teacher", {}).get("unique_action_count"),
        "seconds": output["seconds"],
    }, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
