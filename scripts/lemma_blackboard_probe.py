#!/usr/bin/env python3
"""Deterministically verify the monotone lemma-blackboard invariants."""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "scripts"))

from curriculum_blackboard import LemmaBlackboard  # noqa: E402
import midpoint_curriculum_probe as curriculum  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / ".artifacts" / "lemma_blackboard_probe.json",
    )
    parser.add_argument("--verify-judge", action="store_true")
    parser.add_argument("--judge-timeout", type=int, default=30)
    args = parser.parse_args()

    started = time.monotonic()
    spec = curriculum.CURRICULUM["right_square_train_hard2_0107"]
    experiment = spec["capability_experiment"]
    problem = curriculum.problem_by_id(spec["problem_id"])
    h_eq = curriculum.solver.parse_equation(problem["equation1"])
    g_eq = curriculum.solver.parse_equation(problem["equation2"])

    full_body, full_state = curriculum.run_action_body(
        experiment["full_mechanical_action"], h_eq, g_eq
    )
    withheld_body, withheld_state = curriculum.run_action_body(
        experiment["full_mechanical_action"],
        h_eq,
        g_eq,
        capability_mask=experiment["curriculum_mask"],
    )

    blackboard = LemmaBlackboard()
    partial_body, partial_state = curriculum.run_action_body(
        curriculum.BAD_RIGHT_SQUARE_INCOMPLETE,
        h_eq,
        g_eq,
        capability_mask=experiment["curriculum_mask"],
    )
    partial_update = blackboard.absorb_mechanical_state(
        curriculum.BAD_RIGHT_SQUARE_INCOMPLETE,
        partial_state,
        round_index=1,
    )
    second_action = {
        "kind": "midpoint",
        "lemma": "a ◇ b = b ◇ b",
        "why": "new node only; the blackboard must retain square_absorb",
    }
    merged_action, merge_state = blackboard.materialize_action(second_action, round_index=2)
    merged_body, merged_state = curriculum.run_action_body(
        merged_action or {},
        h_eq,
        g_eq,
        capability_mask=experiment["curriculum_mask"],
    )
    merged_update = blackboard.absorb_mechanical_state(
        merged_action,
        merged_state,
        round_index=2,
    )
    judge = (
        curriculum.judge_true_body(problem, merged_body, args.judge_timeout)
        if args.verify_judge
        else None
    )
    negative_body, negative_state = curriculum.run_action_body(
        merged_action or {},
        h_eq,
        g_eq,
        capability_mask=experiment["negative_control_mask"],
    )

    refutation_board = LemmaBlackboard()
    false_action = {
        "kind": "midpoint",
        "lemma": "x = (y ◇ (y ◇ z)) ◇ x",
    }
    false_body, false_state = curriculum.run_action_body(
        false_action,
        h_eq,
        g_eq,
        capability_mask=experiment["curriculum_mask"],
    )
    refutation_update = refutation_board.absorb_mechanical_state(
        false_action,
        false_state,
        round_index=1,
    )
    alpha_repeat = {
        "kind": "midpoint",
        "lemma": "p = (q ◇ (q ◇ r)) ◇ p",
    }
    blocked_action, blocked_state = refutation_board.materialize_action(
        alpha_repeat,
        round_index=2,
    )

    checks = {
        "full_specialized_baseline_succeeds": bool(full_body),
        "specialized_shortcut_is_withheld": (
            not bool(withheld_body)
            and (withheld_state or {}).get("status") == "withheld_for_curriculum"
        ),
        "partial_action_does_not_solve": not bool(partial_body),
        "partial_action_adds_one_trusted_node": len(partial_update["added_trusted"]) == 1,
        "new_action_retains_trusted_node": (
            merge_state.get("retained_node_count") == 1
            and len((merged_action or {}).get("lemmas") or []) == 2
        ),
        "merged_generic_action_succeeds_without_focused_fallback": (
            bool(merged_body) and (merged_state or {}).get("status") == "body_built"
        ),
        "merged_action_judge_accepted": None if judge is None else bool(judge.get("accepted")),
        "negative_control_removes_generic_recovery": not bool(negative_body),
        "small_model_refutation_is_recorded": len(refutation_update["added_refuted"]) == 1,
        "alpha_equivalent_refuted_repeat_is_blocked": (
            blocked_action is None
            and blocked_state.get("status") == "blocked_refuted_repetition"
        ),
        "trusted_state_is_monotone": len(blackboard.trusted_nodes) == 2,
    }
    output = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "case_id": "right_square_train_hard2_0107",
        "checks": checks,
        "passed": all(value is True for value in checks.values() if value is not None),
        "full_state": curriculum.summarize_state(full_state),
        "withheld_state": curriculum.summarize_state(withheld_state),
        "partial_state": curriculum.summarize_state(partial_state),
        "partial_update": partial_update,
        "merge_state": merge_state,
        "merged_action": merged_action,
        "merged_state": curriculum.summarize_state(merged_state),
        "merged_update": merged_update,
        "judge": judge,
        "negative_state": curriculum.summarize_state(negative_state),
        "blackboard": blackboard.snapshot(),
        "false_state": curriculum.summarize_state(false_state),
        "refutation_update": refutation_update,
        "blocked_state": blocked_state,
        "refutation_blackboard": refutation_board.snapshot(),
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
