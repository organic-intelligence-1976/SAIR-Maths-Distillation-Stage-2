#!/usr/bin/env python3
"""Verify structural lesson transfer on an alpha-renamed disguised continuation."""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from research_system.curriculum import CurriculumCase, reference_cases  # noqa: E402
from research_system.distillation import VerifiedDistiller  # noqa: E402
from research_system.executor import MechanicalExecutor  # noqa: E402
from research_system.experience import ExperienceStore  # noqa: E402
from research_system.orchestrator import ResearchEpisodeRunner  # noqa: E402
from research_system.planner import RetrievedLessonPlanner, ScriptedPlanner  # noqa: E402
from research_system.protocol import ProblemSpec  # noqa: E402
from research_system.semantics import SemanticService  # noqa: E402
from research_system.verifier import OfficialLeanVerifier  # noqa: E402


def make_runner(
    *,
    store: ExperienceStore,
    retrieval_limit: int,
    judge_timeout: int,
    artifact_dir: Path,
) -> ResearchEpisodeRunner:
    return ResearchEpisodeRunner(
        semantics=SemanticService(ROOT / "data" / "semantics" / "austin_implications.json"),
        executor=MechanicalExecutor(),
        verifier=OfficialLeanVerifier(timeout_seconds=judge_timeout, artifact_dir=artifact_dir),
        store=store,
        distiller=VerifiedDistiller(),
        retrieval_limit=retrieval_limit,
    )


def target_case() -> CurriculumCase:
    source = reference_cases()["reference_true_right_square"]
    problem = ProblemSpec(
        id="structural_holdout_right_square_alpha_orientation",
        eq1_id=source.problem.eq1_id,
        eq2_id=source.problem.eq2_id,
        equation1="((b ◇ (b ◇ c)) ◇ (a ◇ a)) = a",
        equation2="(a ◇ ((b ◇ (a ◇ b)) ◇ a)) = a",
        answer=True,
    )
    return CurriculumCase(
        case_id="structural_holdout_right_square_alpha_orientation",
        problem=problem,
        actions=(),
        capability_mask={"disabled": ["tool:right_square_chain"]},
        negative_control_mask={
            "disabled": ["tool:right_square_chain", "primitive:generic_midpoint_prover"],
        },
        expected_verdict="true",
        max_rounds=2,
        split_label="sealed_test",
        tags=("true", "structural_retrieval", "alpha_renamed", "orientation_disguised", "partial_progress"),
    )


def unrelated_case(source: CurriculumCase) -> CurriculumCase:
    return CurriculumCase(
        case_id="structural_retrieval_unrelated_negative",
        problem=ProblemSpec(
            id="structural_retrieval_unrelated_negative",
            eq1_id=source.problem.eq1_id,
            eq2_id=source.problem.eq2_id,
            equation1="x ◇ y = x",
            equation2="u ◇ v = u",
            answer=True,
        ),
        actions=(),
        capability_mask=source.capability_mask,
        expected_verdict="true",
        max_rounds=1,
        split_label="sealed_test",
        tags=("negative_control", "structurally_unrelated"),
    )


def selected_lemma_count(episode: dict) -> int | None:
    for attempt in episode.get("attempts") or []:
        trace = attempt.get("planner_trace") if isinstance(attempt, dict) else None
        if isinstance(trace, dict) and trace.get("source") == "verified_structural_retrieval":
            return trace.get("selected_node_count")
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / ".artifacts" / "structural_retrieval" / "probe.json",
    )
    parser.add_argument(
        "--store",
        type=Path,
        default=ROOT / ".artifacts" / "structural_retrieval" / "experience",
    )
    parser.add_argument("--judge-timeout", type=int, default=45)
    args = parser.parse_args()

    started = time.monotonic()
    store = ExperienceStore(args.store)
    artifact_dir = args.output.parent / "judge"
    source = reference_cases()["reference_true_right_square"]
    training_runner = make_runner(
        store=store,
        retrieval_limit=0,
        judge_timeout=args.judge_timeout,
        artifact_dir=artifact_dir,
    )
    source_episode, source_artifact = training_runner.run(
        source,
        ScriptedPlanner(list(source.actions), name="structural_source_scripted"),
    )

    target = target_case()
    partial_case = CurriculumCase(
        **{
            **target.__dict__,
            "case_id": f"{target.case_id}__partial",
            "max_rounds": 1,
            "split_label": "development",
        }
    )
    partial_episode, _ = training_runner.run(
        partial_case,
        ScriptedPlanner([
            {
                "kind": "tool_call",
                "tool": "lemma_chain",
                "target": "goal",
                "lemmas": [{"name": "square_absorb", "equation": "u ◇ (v ◇ v) = v"}],
            }
        ], name="structural_partial_plan_seed"),
    )
    partial_snapshot = partial_episode.to_mapping()

    no_retrieval_runner = make_runner(
        store=store,
        retrieval_limit=0,
        judge_timeout=args.judge_timeout,
        artifact_dir=artifact_dir,
    )
    no_retrieval_episode, _ = no_retrieval_runner.run(
        target,
        RetrievedLessonPlanner(name="retrieval_disabled_control"),
        resume_from=partial_snapshot,
    )

    retrieval_runner = make_runner(
        store=store,
        retrieval_limit=4,
        judge_timeout=args.judge_timeout,
        artifact_dir=artifact_dir,
    )
    transfer_episode, transfer_artifact = retrieval_runner.run(
        target,
        RetrievedLessonPlanner(),
        resume_from=partial_snapshot,
    )
    negative = unrelated_case(target)
    negative_episode, _ = retrieval_runner.run(
        negative,
        RetrievedLessonPlanner(name="structural_negative_control"),
    )

    source_map = source_episode.to_mapping()
    partial_map = partial_episode.to_mapping()
    no_retrieval_map = no_retrieval_episode.to_mapping()
    transfer_map = transfer_episode.to_mapping()
    negative_map = negative_episode.to_mapping()
    checks = {
        "source_verified_and_distilled": (
            source_episode.accepted
            and source_artifact is not None
            and source_artifact.payload.get("lesson_schema") == "sair-proof-plan-lesson-v1"
        ),
        "partial_plan_is_verified_but_incomplete": (
            not partial_episode.accepted
            and len(partial_episode.blackboard.get("trusted_nodes") or []) == 1
        ),
        "retrieval_is_load_bearing": (
            not no_retrieval_episode.accepted
            and transfer_episode.accepted
            and selected_lemma_count(transfer_map) == 1
        ),
        "target_was_mechanically_reverified": (
            (transfer_episode.verification or {}).get("status") == "accepted"
            and transfer_artifact is not None
        ),
        "unrelated_lesson_is_rejected": (
            not negative_episode.accepted
            and not (negative_episode.metadata.get("retrieval") or {}).get("final_artifact_ids")
        ),
    }
    output = {
        "schema_version": 1,
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "checks": checks,
        "passed": all(checks.values()),
        "source": {"episode": source_map, "artifact": source_artifact.to_mapping() if source_artifact else None},
        "partial_target": partial_map,
        "no_retrieval_control": no_retrieval_map,
        "retrieval_transfer": {
            "episode": transfer_map,
            "artifact": transfer_artifact.to_mapping() if transfer_artifact else None,
        },
        "unrelated_negative_control": negative_map,
        "experience_store": store.summary(),
        "seconds": round(time.monotonic() - started, 3),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({
        "output": str(args.output),
        "passed": output["passed"],
        "checks": checks,
        "source_artifact_id": source_artifact.artifact_id if source_artifact else None,
        "transfer_selected_node_count": selected_lemma_count(transfer_map),
        "seconds": output["seconds"],
    }, ensure_ascii=False))
    return 0 if output["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
