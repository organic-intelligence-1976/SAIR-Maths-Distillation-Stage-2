#!/usr/bin/env python3
"""Run verified bounded-beam teacher search and ordinary-budget student replay."""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from research_system.curriculum import CurriculumCase, load_problem  # noqa: E402
from research_system.distillation import VerifiedDistiller  # noqa: E402
from research_system.executor import MechanicalExecutor  # noqa: E402
from research_system.experience import ExperienceStore  # noqa: E402
from research_system.orchestrator import ResearchEpisodeRunner  # noqa: E402
from research_system.planner import ContextAugmentingPlanner, OpenAICompatiblePlanner  # noqa: E402
from research_system.semantics import SemanticService  # noqa: E402
from research_system.teacher import (  # noqa: E402
    TeacherSearchConfig,
    TeacherStudentSearch,
    action_signature,
)
from research_system.verifier import OfficialLeanVerifier  # noqa: E402


def load_config(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("LLM config must be a JSON object")
    return payload


def migrate_legacy_resume(payload: dict, report: dict) -> dict:
    """Recover a finite-action beam from reports written before resume_state existed."""
    if isinstance(report.get("resume_state"), dict):
        return report
    generations = report.get("teacher", {}).get("generations") or []
    if not generations:
        return report
    selected = set(generations[-1].get("selected_branch_ids") or [])
    candidates = [
        candidate
        for generation in generations
        for candidate in generation.get("candidates") or []
        if isinstance(candidate, dict)
    ]
    selected_candidates = [
        candidate for candidate in candidates if candidate.get("branch_id") in selected
    ]
    store_root = (payload.get("experience_store") or {}).get("root")
    if not selected_candidates or not store_root:
        return report
    episodes_path = Path(store_root) / "episodes.jsonl"
    if not episodes_path.is_file():
        return report
    episodes = {}
    for line in episodes_path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        episode = json.loads(line)
        branch_id = (
            episode.get("metadata", {})
            .get("teacher_student", {})
            .get("branch_id")
        )
        if branch_id:
            episodes[str(branch_id)] = episode
    beam = []
    for candidate in selected_candidates:
        branch_id = str(candidate.get("branch_id"))
        episode = episodes.get(branch_id)
        actions = candidate.get("actions") or []
        if episode is None or any(
            isinstance(action.get("code"), dict) or isinstance(action.get("proof"), dict)
            for action in actions
            if isinstance(action, dict)
        ):
            continue
        beam.append({
            "branch_id": branch_id,
            "parent_id": candidate.get("parent_id"),
            "depth": candidate.get("depth"),
            "actions": actions,
            "action": candidate.get("action") or {},
            "action_signature": candidate.get("action_signature"),
            "episode": episode,
            "score": candidate.get("score"),
            "score_breakdown": candidate.get("score_breakdown") or {},
            "planner_trace": candidate.get("planner_trace"),
        })
    if not beam:
        return report
    seen_actions = {}
    for candidate in candidates:
        action = candidate.get("action")
        if isinstance(action, dict):
            seen_actions[action_signature(action)] = action
    migrated = dict(report)
    migrated["resume_state"] = {
        "version": "sair-teacher-student-v1",
        "case_id": report.get("case_id"),
        "next_depth": max(int(row.get("depth") or 0) for row in beam) + 1,
        "beam": beam,
        "seen_actions": seen_actions,
        "provider_failure_count": int(
            report.get("teacher", {}).get("provider_failure_count") or 0
        ),
        "generations": generations,
        "migrated_from_legacy_report": True,
    }
    return migrated


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--problem-id",
        action="append",
        help="Official problem ID; repeat for multiple cases (default: hard2_0093)",
    )
    parser.add_argument(
        "--teacher-llm-config",
        type=Path,
        default=ROOT / ".artifacts" / "team_y_suspected_top20_config.json",
    )
    parser.add_argument(
        "--student-llm-config",
        type=Path,
        help="Defaults to the teacher config, but runs with the smaller student round budget",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / ".artifacts" / "teacher_student_search.json",
    )
    parser.add_argument(
        "--store",
        type=Path,
        default=ROOT / ".artifacts" / "research_system" / "teacher_experience",
    )
    parser.add_argument("--beam-width", type=int, default=3)
    parser.add_argument("--proposals-per-branch", type=int, default=4)
    parser.add_argument("--max-depth", type=int, default=4)
    parser.add_argument("--branch-rounds", type=int, default=2)
    parser.add_argument("--student-rounds", type=int, default=4)
    parser.add_argument("--exploration-fraction", type=float, default=0.25)
    parser.add_argument(
        "--focus",
        choices=("auto", "general", "finite_symbolic", "infinite_model"),
        default="auto",
    )
    parser.add_argument("--proposal-workers", type=int, default=4)
    parser.add_argument(
        "--size-probe-max",
        type=int,
        choices=(2, 3, 4, 5),
        default=4,
        help="Largest carrier to exhaustively preflight; size 5 may take tens of seconds",
    )
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--llm-timeout", type=float, default=120.0)
    parser.add_argument("--judge-timeout", type=int, default=90)
    parser.add_argument(
        "--skip-student",
        action="store_true",
        help="Run teacher discovery and mechanical replay only",
    )
    parser.add_argument(
        "--skip-no-lesson-counterfactual",
        action="store_true",
        help="Skip the ordinary-model no-lesson attribution control",
    )
    parser.add_argument(
        "--resume-report",
        type=Path,
        help="Continue the selected beam stored in a previous teacher-search report",
    )
    args = parser.parse_args()

    if not args.teacher_llm_config.is_file():
        parser.error(f"teacher LLM config does not exist: {args.teacher_llm_config}")
    student_path = args.student_llm_config or args.teacher_llm_config
    if not args.skip_student and not student_path.is_file():
        parser.error(f"student LLM config does not exist: {student_path}")
    try:
        teacher_config = load_config(args.teacher_llm_config)
        student_config = load_config(student_path) if not args.skip_student else None
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        parser.error(str(exc))

    config = TeacherSearchConfig(
        beam_width=args.beam_width,
        proposals_per_branch=args.proposals_per_branch,
        max_depth=args.max_depth,
        branch_rounds=args.branch_rounds,
        student_rounds=args.student_rounds,
        exploration_fraction=args.exploration_fraction,
        run_no_lesson_counterfactual=not args.skip_no_lesson_counterfactual,
        focus=args.focus,
        proposal_workers=args.proposal_workers,
        size_probe_max=args.size_probe_max,
        seed=args.seed,
    )
    store = ExperienceStore(args.store)
    runner = ResearchEpisodeRunner(
        semantics=SemanticService(ROOT / "data" / "semantics" / "austin_implications.json"),
        executor=MechanicalExecutor(),
        verifier=OfficialLeanVerifier(timeout_seconds=args.judge_timeout),
        store=store,
        distiller=VerifiedDistiller(),
    )

    def student_factory(lesson: dict | None):
        assert student_config is not None
        planner = OpenAICompatiblePlanner(student_config, timeout=args.llm_timeout)
        additions = {"teacher_lesson": lesson} if lesson is not None else {}
        return ContextAugmentingPlanner(
            planner,
            additions,
            name="ordinary_student_with_lesson" if lesson is not None else "ordinary_student_no_lesson",
        )

    started = time.monotonic()
    prior_reports: dict[str, dict] = {}
    if args.resume_report is not None:
        if not args.resume_report.is_file():
            parser.error(f"resume report does not exist: {args.resume_report}")
        try:
            prior_payload = json.loads(args.resume_report.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            parser.error(f"invalid resume report: {exc}")
        prior_reports = {
            str(report.get("case_id")): migrate_legacy_resume(prior_payload, report)
            for report in prior_payload.get("reports") or []
            if isinstance(report, dict) and report.get("case_id")
        }
    reports = []
    for problem_id in args.problem_id or ["hard2_0093"]:
        try:
            problem = load_problem(problem_id)
        except KeyError as exc:
            parser.error(str(exc))
        expected = "true" if problem.answer else "false"
        case = CurriculumCase(
            case_id=f"teacher_{problem_id}",
            problem=problem,
            actions=(),
            expected_verdict=expected,
            max_rounds=config.max_depth,
            tags=("teacher_search", expected),
        )
        search = TeacherStudentSearch(
            runner,
            OpenAICompatiblePlanner(teacher_config, timeout=args.llm_timeout),
            config=config,
            student_planner_factory=None if args.skip_student else student_factory,
            teacher_planner_factory=lambda: OpenAICompatiblePlanner(
                teacher_config,
                timeout=args.llm_timeout,
            ),
        )
        prior = prior_reports.get(case.case_id)
        if args.resume_report is not None and prior is None:
            parser.error(
                f"resume report has no case {case.case_id}: {args.resume_report}"
            )
        reports.append(search.run(case, resume_from=prior))

    output = {
        "schema_version": 1,
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "teacher_config": {
            "path": str(args.teacher_llm_config),
            "model": (teacher_config.get("llm") or teacher_config).get("model"),
        },
        "student_config": {
            "path": str(student_path),
            "model": ((student_config or {}).get("llm") or student_config or {}).get("model"),
        } if student_config is not None else None,
        "search_config": config.normalized().__dict__,
        "resume_report": str(args.resume_report) if args.resume_report else None,
        "reports": reports,
        "experience_store": store.summary(),
        "seconds": round(time.monotonic() - started, 3),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(output, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({
        "output": str(args.output),
        "outcomes": [
            {
                "case_id": report.get("case_id"),
                "outcome": report.get("outcome"),
                "teacher_actions": report.get("teacher", {}).get("unique_action_count"),
                "load_bearing": report.get("student", {}).get("load_bearing"),
                "seconds": report.get("seconds"),
            }
            for report in reports
        ],
        "experience_store": output["experience_store"],
        "seconds": output["seconds"],
    }, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
