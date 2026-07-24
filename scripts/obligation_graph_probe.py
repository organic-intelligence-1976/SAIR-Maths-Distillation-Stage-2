#!/usr/bin/env python3
"""Exercise a one-turn diverse proof plan with automatic dependency continuation."""

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
from research_system.distillation import VerifiedDistiller  # noqa: E402
from research_system.executor import MechanicalExecutor  # noqa: E402
from research_system.experience import ExperienceStore  # noqa: E402
from research_system.orchestrator import ResearchEpisodeRunner  # noqa: E402
from research_system.planner import ScriptedPlanner  # noqa: E402
from research_system.semantics import SemanticService  # noqa: E402
from research_system.verifier import OfficialLeanVerifier  # noqa: E402


PLAN = {
    "kind": "proof_plan",
    "max_parallel": 3,
    "nodes": [
        {
            "id": "square_absorb",
            "equation": "u ◇ (v ◇ v) = v",
            "family_id": "square_normalization",
            "mechanism": "derive a square-absorption normal form",
            "alternative_group": "root_route",
            "advances": "root",
        },
        {
            "id": "left_projection_adversary",
            "equation": "a ◇ b = a",
            "family_id": "projection",
            "mechanism": "test whether the hypothesis collapses to left projection",
            "alternative_group": "root_route",
            "advances": "root",
        },
        {
            "id": "right_square",
            "equation": "u ◇ v = v ◇ v",
            "family_id": "square_normalization",
            "mechanism": "strengthen square absorption to a right-square normal form",
            "depends_on": ["square_absorb"],
            "advances": "root",
        },
    ],
}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / ".artifacts" / "obligation_graph" / "probe.json",
    )
    parser.add_argument(
        "--store",
        type=Path,
        default=ROOT / ".artifacts" / "obligation_graph" / "experience",
    )
    parser.add_argument("--judge-timeout", type=int, default=45)
    args = parser.parse_args()

    started = time.monotonic()
    case = replace(
        reference_cases()["reference_true_right_square"],
        case_id="obligation_graph_right_square",
        actions=(),
        max_rounds=2,
        split_label="development",
        tags=("true", "obligation_graph", "approach_portfolio", "automatic_dependency"),
    )
    store = ExperienceStore(args.store)
    runner = ResearchEpisodeRunner(
        semantics=SemanticService(ROOT / "data" / "semantics" / "austin_implications.json"),
        executor=MechanicalExecutor(),
        verifier=OfficialLeanVerifier(
            timeout_seconds=args.judge_timeout,
            artifact_dir=args.output.parent / "judge",
        ),
        store=store,
        distiller=VerifiedDistiller(),
    )
    episode, artifact = runner.run(
        case,
        ScriptedPlanner([PLAN], name="one_turn_diverse_obligation_plan"),
    )
    negative_case = replace(
        case,
        case_id=f"{case.case_id}__negative",
        capability_mask={
            "disabled": ["tool:right_square_chain", "primitive:generic_midpoint_prover"],
        },
    )
    negative_episode, _ = runner.run(
        negative_case,
        ScriptedPlanner([PLAN], name="one_turn_obligation_plan_negative"),
    )

    episode_map = episode.to_mapping()
    negative_map = negative_episode.to_mapping()
    nodes = {row["node_id"]: row for row in episode.obligations.get("nodes") or []}
    families = {row["family_id"]: row for row in episode.obligations.get("families") or []}
    checks = {
        "one_planner_turn_then_automatic_dependency": (
            len(episode.attempts) == 2
            and episode.attempts[1].get("planner_trace", {}).get("source")
            == "automatic_dependency_scheduler"
        ),
        "diverse_initial_portfolio": (
            set(episode.attempts[0].get("obligation_preflight", {}).get("selected_families") or [])
            == {"square_normalization", "left_projection"}
        ),
        "adversarial_alternative_refuted": (
            nodes.get("left_projection_adversary", {}).get("status") == "refuted"
        ),
        "dependency_chain_mechanically_proved": (
            nodes.get("square_absorb", {}).get("status") == "proved"
            and nodes.get("right_square", {}).get("status") == "proved"
            and nodes.get("right_square", {}).get("depends_on") == ["square_absorb"]
        ),
        "family_registry_retained": (
            set(families) == {"square_normalization", "left_projection"}
            and families["square_normalization"]["node_count"] == 2
        ),
        "final_proof_accepted": episode.accepted and (episode.verification or {}).get("status") == "accepted",
        "generic_worker_is_load_bearing": not negative_episode.accepted,
        "distilled_lesson_retains_graph_metadata": (
            artifact is not None
            and all(
                node.get("family_id") and node.get("mechanism_signature")
                for node in artifact.payload.get("plan_nodes") or []
            )
        ),
    }
    output = {
        "schema_version": 1,
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "passed": all(checks.values()),
        "checks": checks,
        "plan": PLAN,
        "episode": episode_map,
        "artifact": artifact.to_mapping() if artifact else None,
        "negative_control": negative_map,
        "experience_store": store.summary(),
        "seconds": round(time.monotonic() - started, 3),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({
        "output": str(args.output),
        "passed": output["passed"],
        "checks": checks,
        "seconds": output["seconds"],
    }, ensure_ascii=False))
    return 0 if output["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
