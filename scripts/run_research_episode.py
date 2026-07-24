#!/usr/bin/env python3
"""Run the modular walking skeleton on verified reference curriculum cases."""

from __future__ import annotations

import argparse
import json
import sys
import time
from dataclasses import replace
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from research_system.curriculum import reference_cases  # noqa: E402
from research_system.budget import budget_policy_record, load_budget_policy  # noqa: E402
from research_system.distillation import VerifiedDistiller  # noqa: E402
from research_system.evaluation import CurriculumEvaluator  # noqa: E402
from research_system.executor import MechanicalExecutor  # noqa: E402
from research_system.experience import ExperienceStore  # noqa: E402
from research_system.orchestrator import ResearchEpisodeRunner  # noqa: E402
from research_system.planner import OpenAICompatiblePlanner  # noqa: E402
from research_system.semantics import SemanticService  # noqa: E402
from research_system.verifier import OfficialLeanVerifier  # noqa: E402


def resume_episodes(path: Path) -> dict[str, dict]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    episodes: dict[str, dict] = {}
    for report in payload.get("reports") or []:
        if not isinstance(report, dict):
            continue
        curriculum = report.get("curriculum")
        episode = curriculum.get("episode") if isinstance(curriculum, dict) else None
        if isinstance(episode, dict) and isinstance(episode.get("case_id"), str):
            episodes[episode["case_id"]] = episode
    return episodes


def main() -> int:
    cases = reference_cases()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", action="append", choices=sorted(cases), help="Reference case; repeat or omit for all")
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / ".artifacts" / "research_system" / "reference_report.json",
    )
    parser.add_argument(
        "--store",
        type=Path,
        default=ROOT / ".artifacts" / "research_system" / "experience",
    )
    parser.add_argument("--judge-timeout", type=int, default=45)
    parser.add_argument(
        "--planner",
        choices=("scripted", "llm"),
        default="scripted",
        help="Use known reference actions or exercise the live stateful System-2 loop",
    )
    parser.add_argument(
        "--llm-config",
        type=Path,
        default=ROOT / ".artifacts" / "openrouter_fast_config.json",
        help="Runner-style JSON containing an llm configuration block",
    )
    parser.add_argument("--llm-timeout", type=float, default=90.0)
    parser.add_argument(
        "--retrieval-limit",
        type=int,
        default=0,
        help="Verified artifacts to retrieve into each LLM turn; zero gives a clean live attempt",
    )
    parser.add_argument("--max-rounds", type=int, help="Override the case round limit")
    parser.add_argument(
        "--budget-policy",
        type=Path,
        help="JSON midpoint budget genotype; recorded in every episode and applied to lemma actions",
    )
    parser.add_argument(
        "--resume-report",
        type=Path,
        help="Continue from mechanically verified blackboard state in a prior report",
    )
    args = parser.parse_args()

    if args.resume_report is not None and args.planner != "llm":
        parser.error("--resume-report currently applies to --planner llm")

    selected = args.case or (
        ["reference_true_right_square"] if args.planner == "llm" else list(cases)
    )
    try:
        budget_policy = load_budget_policy(args.budget_policy) if args.budget_policy else None
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        parser.error(f"invalid --budget-policy: {exc}")
    store = ExperienceStore(args.store)
    runner = ResearchEpisodeRunner(
        semantics=SemanticService(ROOT / "data" / "semantics" / "austin_implications.json"),
        executor=MechanicalExecutor(budget_policy=budget_policy),
        verifier=OfficialLeanVerifier(timeout_seconds=args.judge_timeout),
        store=store,
        distiller=VerifiedDistiller(),
        retrieval_limit=args.retrieval_limit,
    )
    started = time.monotonic()
    if args.planner == "scripted":
        evaluator = CurriculumEvaluator(runner)
        reports = [evaluator.evaluate(cases[case_id]) for case_id in selected]
    else:
        if not args.llm_config.is_file():
            parser.error(f"LLM config does not exist: {args.llm_config}")
        config = json.loads(args.llm_config.read_text(encoding="utf-8"))
        prior_episodes = resume_episodes(args.resume_report) if args.resume_report else {}
        reports = []
        for case_id in selected:
            case = cases[case_id]
            if args.max_rounds is not None:
                case = replace(case, max_rounds=max(1, args.max_rounds))
            resume_from = prior_episodes.get(case.case_id)
            if args.resume_report is not None and resume_from is None:
                parser.error(
                    f"resume report has no curriculum episode for case {case.case_id}: "
                    f"{args.resume_report}"
                )
            planner = OpenAICompatiblePlanner(config, timeout=args.llm_timeout)
            episode, artifact = runner.run(case, planner, resume_from=resume_from)
            checks = {
                "live_llm_accepted": episode.accepted,
                "expected_verdict_matched": (
                    (episode.verification or {}).get("verdict") == case.expected_verdict
                ),
            }
            reports.append({
                "case_id": case.case_id,
                "eligible": all(checks.values()),
                "checks": checks,
                "curriculum": {
                    "episode": episode.to_mapping(),
                    "artifact": artifact.to_mapping() if artifact else None,
                },
                "full": None,
                "negative": None,
            })
    output = {
        "schema_version": 1,
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "planner_mode": args.planner,
        "retrieval_limit": max(0, args.retrieval_limit),
        "resume_report": str(args.resume_report) if args.resume_report else None,
        "budget_policy": budget_policy_record(budget_policy) if budget_policy is not None else None,
        "reports": reports,
        "all_eligible": all(report["eligible"] for report in reports),
        "experience_store": store.summary(),
        "seconds": round(time.monotonic() - started, 3),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({
        "output": str(args.output),
        "all_eligible": output["all_eligible"],
        "cases": [
            {
                "case_id": report["case_id"],
                "eligible": report["eligible"],
                "checks": report["checks"],
                "outcome": report["curriculum"]["episode"]["outcome"],
                "artifact_kind": (report["curriculum"].get("artifact") or {}).get("kind"),
            }
            for report in reports
        ],
        "experience_store": output["experience_store"],
        "seconds": output["seconds"],
    }, ensure_ascii=False))
    return 0 if output["all_eligible"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
