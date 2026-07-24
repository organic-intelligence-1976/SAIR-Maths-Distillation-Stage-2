#!/usr/bin/env python3
"""Fast contract checks for every walking-skeleton component."""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import baby_solver  # noqa: E402
from research_system.budget import budget_policy_record, mutate_budget_policy  # noqa: E402
from research_system.blackboard import LemmaBlackboard, canonical_equation_signature  # noqa: E402
from research_system.capabilities import CapabilityService  # noqa: E402
from research_system.compiler import CompilationSpec, SubmissionCompiler  # noqa: E402
from research_system.curriculum import CurriculumCase, reference_cases  # noqa: E402
from research_system.distillation import VerifiedDistiller  # noqa: E402
from research_system.experience import ExperienceStore  # noqa: E402
from research_system.integration import IntegrationCatalog  # noqa: E402
from research_system.obligations import ObligationGraph, infer_approach_family  # noqa: E402
from research_system.orchestrator import ResearchEpisodeRunner, compact_mechanical_feedback  # noqa: E402
from research_system.planner import (  # noqa: E402
    FunctionPlanner,
    OpenAICompatiblePlanner,
    RetrievedLessonPlanner,
    ScriptedPlanner,
)
from research_system.protocol import (  # noqa: E402
    EpisodeRecord,
    ExecutionResult,
    ProblemSpec,
    StrategyArtifact,
    VerificationRecord,
)
from research_system.semantics import SemanticService  # noqa: E402
from research_system.structure import dual_equation, problem_structure, structural_similarity  # noqa: E402


def main() -> int:
    checks: dict[str, bool] = {}
    solver_source = (ROOT / "baby_solver.py").read_text(encoding="utf-8")
    checks["reference_baseline_fallback_retired"] = not any(
        marker in solver_source
        for marker in (
            "REFERENCE_SOLVER_B64_ZLIB",
            "reference_namespace",
            "run_reference_mechanical_tool",
            "child_reference",
        )
    )
    checks["native_replacement_categories"] = all(
        name in baby_solver.TOOL_REGISTRY
        for name in (
            "grounding_h",
            "deep_saturation",
            "standard_aux_superposition",
            "goal_superposition",
            "false_model_search",
        )
    )
    replacement_h = baby_solver.parse_equation("(x ◇ y) = (z ◇ x)")
    replacement_g = baby_solver.parse_equation("(a ◇ b) = (c ◇ a)")
    grounding_bodies = list(baby_solver.grounding_h_certificate_bodies(replacement_h, replacement_g))
    saturation_bodies = list(baby_solver.native_saturation_bodies(replacement_h, replacement_g))
    structured_witness = baby_solver.structured_counterexample_search(
        baby_solver.parse_equation("x = x"),
        baby_solver.parse_equation("x = y"),
        max_n=3,
        time_budget=1,
    )
    checks["native_replacement_generation"] = (
        len(grounding_bodies) == 3
        and len(saturation_bodies) == len(baby_solver.NATIVE_SATURATION_CONFIGS)
        and structured_witness is not None
        and structured_witness[0] == 2
    )
    aux_h = baby_solver.parse_equation("x = (x ◇ y) ◇ ((z ◇ y) ◇ y)")
    aux_g = baby_solver.parse_equation("x = (x ◇ y) ◇ (z ◇ (z ◇ w))")
    rowconst = baby_solver.UniversalEquation(
        name="rowconst",
        eq=baby_solver.standard_aux_equation("rowconst"),
        extra_args=[],
    )
    aux_tail, aux_state = baby_solver.standard_aux_tail("rowconst", aux_g, aux_h, rowconst)
    checks["dynamic_aux_consumer"] = (
        aux_tail is not None
        and "h x y w" in aux_tail
        and "rowconst ((x ◇ y))" in aux_tail
        and aux_state.get("status") == "consumed_by_one_h_aux"
    )
    problem = ProblemSpec(
        id="contract",
        eq1_id=1167,
        eq2_id=1763,
        equation1="x = x",
        equation2="x = x",
        answer=False,
    )
    checks["protocol_roundtrip"] = ProblemSpec.from_mapping(problem.to_mapping()) == problem

    semantics = SemanticService(ROOT / "data" / "semantics" / "austin_implications.json")
    semantic = semantics.classify(problem)
    checks["semantic_registry"] = (
        semantic.semantic_class == "austin_implication"
        and semantic.finite_status == "true"
        and not semantics.finite_search_allowed(semantic)
    )

    manifest = CapabilityService().manifest()
    checks["capability_manifest"] = any(
        row.get("capability") == "tool:right_square_chain" for row in manifest["tools"]
    )

    signature = canonical_equation_signature("x ◇ y = y ◇ y")
    checks["alpha_canonicalization"] = signature == canonical_equation_signature("b ◇ b = a ◇ b")
    checks["indexed_feedback_variables"] = (
        canonical_equation_signature("v0 ◇ (v1 ◇ v1) = v1")
        == canonical_equation_signature("a ◇ (b ◇ b) = b")
    )
    source_structure = problem_structure({
        "equation1": "x = (y ◇ (y ◇ z)) ◇ (x ◇ x)",
        "equation2": "x = x ◇ ((y ◇ (x ◇ y)) ◇ x)",
    })
    disguised_structure = problem_structure({
        "equation1": "((b ◇ (b ◇ c)) ◇ (a ◇ a)) = a",
        "equation2": "(a ◇ ((b ◇ (a ◇ b)) ◇ a)) = a",
    })
    structure_score, structure_reasons = structural_similarity(source_structure, disguised_structure)
    checks["structural_alpha_orientation_invariance"] = (
        structure_score == 100.0
        and "exact_alpha_and_orientation_invariant_pair" in structure_reasons
    )
    board = LemmaBlackboard()
    board.refuted_nodes[signature] = {
        "equation": "x ◇ y = y ◇ y",
        "signature": signature,
        "status": "small_model_refuted",
    }
    blocked, blocked_state = board.materialize_action(
        {"kind": "midpoint", "lemma": "a ◇ b = b ◇ b"},
        round_index=1,
    )
    checks["blackboard_refutation_gate"] = blocked is None and blocked_state["status"] == "blocked_refuted_repetition"
    filtered, filtered_state = board.materialize_action(
        {
            "kind": "tool_call",
            "tool": "lemma_chain",
            "lemmas": [
                {"name": "repeated", "equation": "a ◇ b = b ◇ b"},
                {"name": "fresh", "equation": "a ◇ a = a"},
            ],
        },
        round_index=2,
    )
    checks["blackboard_candidate_filter"] = (
        filtered_state["status"] == "refuted_nodes_filtered"
        and len((filtered or {}).get("lemmas") or []) == 1
        and filtered["lemmas"][0]["name"] == "fresh"
    )

    planner = ScriptedPlanner([{"kind": "midpoint", "lemma": "a = a"}])
    checks["scripted_planner"] = planner.next_action({}) is not None and planner.next_action({}) is None
    policy = baby_solver.MidpointBudgetPolicy.from_mapping({
        "total_budget": 8,
        "initial_grant": 1,
        "grant_growth": 2,
        "max_grant": 4,
        "max_grants_per_task": 3,
        "exploration_weight": 0,
        "tie_break_weight": 0,
    })
    broker = baby_solver.RenewableBudgetBroker(policy)
    broker.register("high", base_score=2.0)
    broker.register("low", base_score=1.0)
    first = broker.next_grant()
    assert first is not None
    broker.report(first[0].task_id, "retryable")
    second = broker.next_grant()
    assert second is not None
    broker.report(second[0].task_id, "retryable")
    third = broker.next_grant()
    checks["renewable_budget_fair_initial_grants"] = (
        first[0].task_id == "high"
        and second[0].task_id == "low"
        and third is not None
        and third[0].task_id == "high"
        and third[1] == 2.0
    )
    policy_record = budget_policy_record(policy.to_mapping())
    offspring = mutate_budget_policy(policy.to_mapping(), seed=17)
    checks["budget_policy_genotype"] = (
        policy_record["policy_id"] == policy.policy_id
        and offspring["policy_id"] != policy.policy_id
        and offspring["schema_version"] == "sair-midpoint-budget-v1"
    )

    original_prover = baby_solver.prove_with_assumptions_detailed
    recursive_calls: list[str] = []
    try:
        h_eq = baby_solver.parse_equation("x ◇ y = x")
        g_eq = baby_solver.parse_equation("x = y")
        bridge = baby_solver.UniversalEquation(
            name="bridge",
            eq=baby_solver.parse_equation("a ◇ b = a"),
            extra_args=[],
        )

        def fake_prover(_h, target, assumptions=None, **_kwargs):
            if target["text"] == g_eq["text"]:
                recursive_calls.append("consume")
                if assumptions and any(item.name == "bridge" for item in assumptions):
                    return "intro x y\nexact bridge x y", {"status": "proved"}
            else:
                recursive_calls.append("attain")
                return "intro a b\nrfl", {"status": "proved"}
            return None, {"status": "stuck"}

        baby_solver.prove_with_assumptions_detailed = fake_prover
        recursive_body, recursive_state = baby_solver.generic_midpoint_chain_attempt(
            h_eq,
            g_eq,
            [bridge],
            budget_policy={
                "total_budget": 2,
                "initial_grant": 1,
                "max_grant": 1,
                "max_grants_per_task": 1,
                "consume_priority": 2,
                "attain_priority": 1,
                "exploration_weight": 0,
                "tie_break_weight": 0,
            },
        )
    finally:
        baby_solver.prove_with_assumptions_detailed = original_prover
    checks["speculative_two_leg_recursion"] = (
        recursive_calls[:2] == ["consume", "attain"]
        and recursive_body is not None
        and "have bridge" in recursive_body
        and recursive_state["budget_allocation"]["policy_id"].startswith("midpoint_budget_v1_")
    )
    obligation_graph = ObligationGraph(block_after_attempts=1)
    plan_action = {
        "kind": "proof_plan",
        "max_parallel": 3,
        "nodes": [
            {
                "id": "projection",
                "equation": "a ◇ b = a",
                "family_id": "optimistic_label",
                "mechanism": "derive left projection",
                "alternative_group": "root_bridge",
            },
            {
                "id": "rowconst",
                "equation": "a ◇ b = a ◇ c",
                "family_id": "row_law",
                "mechanism": "derive row constancy",
                "alternative_group": "root_bridge",
            },
            {
                "id": "dependent",
                "equation": "a ◇ a = a",
                "family_id": "idempotence",
                "mechanism": "specialize the projection",
                "depends_on": ["projection"],
            },
        ],
    }
    first_batch, first_graph_state = obligation_graph.prepare_action(
        plan_action,
        blackboard={},
        round_index=1,
    )
    assert first_batch is not None
    obligation_graph.absorb_mechanical_state(
        first_batch,
        {
            "status": "stuck",
            "proved_lemmas": [{"name": "projection", "equation": "a ◇ b = a"}],
            "failed_midpoints": [{
                "name": "rowconst",
                "equation": "a ◇ b = a ◇ c",
                "failure": {"kind": "small_model_refutation"},
            }],
        },
        round_index=1,
    )
    dependent_batch, _ = obligation_graph.materialize_unattempted(
        blackboard={"trusted_nodes": [{"equation": "x ◇ y = x"}]},
        round_index=2,
    )
    checks["obligation_family_diversity_and_dependencies"] = (
        set(first_graph_state["selected_families"]) == {"left_projection", "row_constancy"}
        and infer_approach_family("u ◇ (v ◇ v) = v", "misc") == "square_normalization"
        and dependent_batch is not None
        and [row["name"] for row in dependent_batch["lemmas"]] == ["dependent"]
        and obligation_graph.nodes["rowconst"].status == "refuted"
    )
    resumed_obligation_graph = ObligationGraph.from_snapshot(obligation_graph.snapshot())
    checks["obligation_graph_resume"] = (
        resumed_obligation_graph.nodes["projection"].status == "proved"
        and resumed_obligation_graph.nodes["rowconst"].status == "refuted"
        and resumed_obligation_graph.nodes["dependent"].depends_on == ["projection"]
    )
    blocked_graph = ObligationGraph(block_after_attempts=1)
    blocked_action = {
        "kind": "proof_plan",
        "nodes": [{
            "id": "blocked_bridge",
            "equation": "a ◇ (b ◇ c) = a",
            "family_id": "contraction",
            "mechanism": "direct contraction search",
        }],
    }
    blocked_batch, _ = blocked_graph.prepare_action(blocked_action, blackboard={}, round_index=1)
    assert blocked_batch is not None
    blocked_graph.absorb_mechanical_state(blocked_batch, {"status": "stuck"}, round_index=1)
    no_reopen, no_reopen_state = blocked_graph.prepare_action(blocked_action, blackboard={}, round_index=2)
    reopened = {
        **blocked_action,
        "nodes": [{
            **blocked_action["nodes"][0],
            "mechanism": "orient a completion rule through square normal forms",
            "reopen_novelty": "use a square-normal-form invariant before contraction",
        }],
    }
    reopen_batch, reopen_state = blocked_graph.prepare_action(reopened, blackboard={}, round_index=3)
    checks["obligation_block_and_novelty_reopen"] = (
        blocked_graph.nodes["blocked_bridge"].reopen_count == 1
        and no_reopen is None
        and no_reopen_state["ingest"][0]["status"] == "rejected_blocked_without_novelty"
        and reopen_batch is not None
        and reopen_state["ingest"][0]["status"] == "reopened_with_novelty"
    )
    checks["reference_curriculum_lanes"] = set(reference_cases()) == {
        "reference_true_right_square",
        "reference_finite_false",
        "reference_infinite_false",
    }

    class FakeExecutor:
        name = "fake_stateful_executor"

        def __init__(self) -> None:
            self.actions: list[dict] = []

        @staticmethod
        def normalize(action: dict) -> tuple[dict, None]:
            return action, None

        def execute(self, problem, action, **kwargs) -> ExecutionResult:
            del problem, kwargs
            self.actions.append(action)
            if len(self.actions) == 1:
                return ExecutionResult(
                    status="mechanical_stuck",
                    submitted_action=action,
                    state={
                        "kind": "midpoint_chain_attempt",
                        "status": "proved_midpoints_not_consumed",
                        "proved_lemmas": [
                            {"name": "first", "equation": "(a ◇ a) = a"},
                        ],
                        "need_hint": "Retain the proved node and add one missing bridge.",
                    },
                )
            return ExecutionResult(
                status="candidate_ready",
                submitted_action=action,
                body="intro G _ h\nintro x\nsimpa using h x",
                state={
                    "kind": "FakeProofState",
                    "status": "candidate_ready",
                    "proved_lemmas": [
                        {"name": "first", "equation": "(a ◇ a) = a"},
                        {"name": "second", "equation": "(a ◇ b) = a"},
                    ],
                },
            )

    class FakeVerifier:
        def verify(self, problem, execution, *, profile="competition") -> VerificationRecord:
            del problem, execution
            return VerificationRecord(
                status="accepted",
                accepted=True,
                verdict="true",
                profile=profile,
            )

    live_contexts: list[dict] = []

    def stateful_plan(context: dict) -> dict:
        live_contexts.append(context)
        if context["round"] == 1:
            return {"kind": "midpoint", "lemma": "a ◇ a = a"}
        return {"kind": "midpoint", "lemma": "a ◇ b = a"}

    fake_executor = FakeExecutor()
    stateful_runner = ResearchEpisodeRunner(
        semantics=semantics,
        executor=fake_executor,
        verifier=FakeVerifier(),
    )
    stateful_case = CurriculumCase(
        case_id="contract_stateful_system2",
        problem=ProblemSpec(
            id="contract_stateful",
            eq1_id=1,
            eq2_id=2,
            equation1="x = x",
            equation2="x = x",
            answer=True,
        ),
        actions=(),
        max_rounds=2,
    )
    stateful_episode, _ = stateful_runner.run(
        stateful_case,
        FunctionPlanner(stateful_plan, name="fake_live_system2"),
    )
    checks["stateful_system2_blackboard"] = (
        stateful_episode.accepted
        and len(live_contexts) == 2
        and len(live_contexts[1]["blackboard"]["trusted_nodes"]) == 1
        and len(fake_executor.actions[1].get("lemmas") or []) == 2
    )
    resumed_board = LemmaBlackboard.from_verified_snapshot(stateful_episode.blackboard)
    checks["verified_episode_resume"] = (
        len(resumed_board.trusted_nodes) == 2
        and not resumed_board.refuted_nodes
        and resumed_board.events[0].get("status") == "verified_snapshot_loaded"
    )
    checks["stateful_system2_feedback"] = (
        live_contexts[1]["recent_observations"][0].get("proved_lemmas")
        == [{"name": "first", "equation": "(a ◇ a) = a"}]
        and bool(live_contexts[1].get("capability_manifest"))
    )

    class DagExecutor:
        name = "fake_dag_executor"

        def __init__(self) -> None:
            self.actions: list[dict] = []

        @staticmethod
        def normalize(action: dict) -> tuple[dict, None]:
            return action, None

        def execute(self, problem, action, **kwargs) -> ExecutionResult:
            del problem, kwargs
            self.actions.append(action)
            if len(self.actions) == 1:
                return ExecutionResult(
                    status="mechanical_stuck",
                    submitted_action=action,
                    state={
                        "kind": "midpoint_chain_attempt",
                        "status": "proved_midpoints_not_consumed",
                        "proved_lemmas": [{"name": "first", "equation": "(a ◇ a) = a"}],
                    },
                )
            return ExecutionResult(
                status="candidate_ready",
                submitted_action=action,
                body="intro G _ h\nintro x\nsimpa using h x",
                state={
                    "kind": "midpoint_chain_attempt",
                    "status": "body_built",
                    "proved_lemmas": [
                        {"name": "first", "equation": "(a ◇ a) = a"},
                        {"name": "second", "equation": "(a ◇ b) = a"},
                    ],
                },
            )

    dag_executor = DagExecutor()
    dag_runner = ResearchEpisodeRunner(
        semantics=semantics,
        executor=dag_executor,
        verifier=FakeVerifier(),
    )
    dag_case = CurriculumCase(
        case_id="contract_obligation_dag",
        problem=ProblemSpec(
            id="contract_obligation_dag",
            eq1_id=3,
            eq2_id=4,
            equation1="x = x",
            equation2="x = x",
            answer=True,
        ),
        actions=(),
        max_rounds=2,
    )
    dag_episode, _ = dag_runner.run(
        dag_case,
        ScriptedPlanner([{
            "kind": "proof_plan",
            "nodes": [
                {
                    "id": "first",
                    "equation": "a ◇ a = a",
                    "family_id": "idempotence",
                    "mechanism": "derive idempotence",
                },
                {
                    "id": "second",
                    "equation": "a ◇ b = a",
                    "family_id": "projection",
                    "mechanism": "strengthen idempotence to projection",
                    "depends_on": ["first"],
                },
            ],
        }], name="single_turn_dag_planner"),
    )
    dag_nodes = {row["node_id"]: row for row in dag_episode.obligations.get("nodes") or []}
    checks["orchestrated_obligation_dag_continuation"] = (
        dag_episode.accepted
        and len(dag_executor.actions) == 2
        and dag_episode.attempts[1]["planner_trace"]["source"] == "automatic_dependency_scheduler"
        and dag_nodes["first"]["status"] == "proved"
        and dag_nodes["second"]["status"] == "proved"
        and dag_nodes["second"]["depends_on"] == ["first"]
    )
    distilled_lesson = VerifiedDistiller().distill(
        stateful_episode,
        ExecutionResult(status="candidate_ready", body="intro x\nrfl"),
    )
    checks["typed_verified_lesson"] = (
        distilled_lesson is not None
        and distilled_lesson.payload.get("lesson_schema") == "sair-proof-plan-lesson-v1"
        and len(distilled_lesson.payload.get("plan_nodes") or []) == 2
        and distilled_lesson.trigger.get("problem_structure", {}).get("structure_version")
        == "sair-equation-structure-v1"
    )
    live_prompt = OpenAICompatiblePlanner.default_prompt(live_contexts[1])
    checks["live_prompt_contract"] = (
        "Trusted blackboard lemmas are retained" in live_prompt
        and "available_tools" in live_prompt
        and "Retain the proved node and add one missing bridge." in live_prompt
    )
    compact = compact_mechanical_feedback({
        "kind": "SearchState",
        "status": "stuck",
        "need_hint": "propose a bridge",
        "stderr": "x" * 10000,
        "goal_search_state": {
            "target": "x = y",
            "closest_pairs": [{"left": "x", "right": "y"}],
        },
        "budget_allocation": {"policy_id": "contract", "events": [{"event": "grant"}]},
    })
    checks["compact_system2_feedback"] = (
        compact.get("need_hint") == "propose a bridge"
        and "stderr" not in compact
        and compact.get("goal_search", {}).get("target") == "x = y"
        and compact.get("budget_allocation", {}).get("policy_id") == "contract"
    )

    with tempfile.TemporaryDirectory(prefix="sair-research-contract-") as tmp:
        temporary = Path(tmp)
        store = ExperienceStore(temporary / "experience")
        episode = EpisodeRecord(
            episode_id="episode_contract",
            case_id="contract",
            problem=problem.to_mapping(),
            semantics=semantic.to_mapping(),
            capability_mask={"disabled": []},
            planner="scripted",
            split_label="development",
            started_at="contract",
            accepted=True,
            outcome="accepted_true",
        )
        store.append_episode(episode)
        artifact = StrategyArtifact(
            artifact_id="strategy_contract",
            kind="proof_plan_schema",
            status="verified",
            deployability="competition_candidate",
            trigger={"semantic_class": "contract"},
            payload={"lemmas": []},
            evidence={"episode_id": episode.episode_id},
        )
        store.append_artifact(artifact)
        assert distilled_lesson is not None
        store.append_artifact(distilled_lesson)
        dual_lesson = StrategyArtifact(
            artifact_id="strategy_dual_contract",
            kind="proof_plan_schema",
            status="verified",
            deployability="competition_candidate",
            trigger={
                "semantic_class": "training_only",
                "problem_structure": source_structure,
                "capability_context": {"disabled": []},
            },
            payload={
                "kind": "verified_proof_plan_lesson",
                "lesson_schema": "sair-proof-plan-lesson-v1",
                "plan_nodes": [{
                    "name": "left_projection",
                    "equation": "x ◇ y = x",
                    "signature": canonical_equation_signature("x ◇ y = x"),
                }],
            },
            evidence={"episode_id": "dual_contract"},
        )
        store.append_artifact(dual_lesson)
        continuation_problem = ProblemSpec(
            id="alpha_disguised_continuation",
            eq1_id=1,
            eq2_id=2,
            equation1="q = q",
            equation2="q = q",
            answer=True,
        )
        partial_board = {
            "trusted_nodes": [{"equation": "z ◇ z = z"}],
        }
        lesson_semantic = str(distilled_lesson.trigger.get("semantic_class"))
        retrieved = store.retrieve_artifacts(
            semantic_class=lesson_semantic,
            problem=continuation_problem,
            capability_mask={"disabled": []},
            blackboard=partial_board,
            limit=3,
        )
        retrieval_action = RetrievedLessonPlanner().next_action({
            "retrieved_artifacts": retrieved,
        })
        unrelated = store.retrieve_artifacts(
            semantic_class=lesson_semantic,
            problem=ProblemSpec(
                id="unrelated",
                eq1_id=1,
                eq2_id=2,
                equation1="x ◇ y = x",
                equation2="x = y",
                answer=True,
            ),
            capability_mask={"disabled": []},
            blackboard={},
            limit=3,
        )
        checks["structural_verified_retrieval"] = (
            len(retrieved) == 1
            and retrieved[0]["artifact_id"] == distilled_lesson.artifact_id
            and retrieved[0]["_retrieval"]["score"] >= 100.0
            and retrieval_action is not None
            and len(retrieval_action.get("lemmas") or []) == 1
            and not unrelated
        )
        dual_retrieved = store.retrieve_artifacts(
            semantic_class="different_target_class",
            problem={
                "equation1": dual_equation("x = (y ◇ (y ◇ z)) ◇ (x ◇ x)"),
                "equation2": dual_equation("x = x ◇ ((y ◇ (x ◇ y)) ◇ x)"),
            },
            capability_mask={"disabled": []},
            blackboard={},
            limit=3,
        )
        dual_action = RetrievedLessonPlanner().next_action({"retrieved_artifacts": dual_retrieved})
        checks["structural_dual_plan_transport"] = (
            len(dual_retrieved) == 1
            and dual_retrieved[0]["artifact_id"] == dual_lesson.artifact_id
            and dual_retrieved[0]["_retrieval"]["plan_transform"] == "magma_dual"
            and dual_action is not None
            and canonical_equation_signature(dual_action["lemmas"][0]["equation"])
            == canonical_equation_signature(dual_equation("x ◇ y = x"))
        )
        checks["experience_store"] = store.summary()["accepted_episode_count"] == 1
        promotion = IntegrationCatalog.promotion_report([artifact.to_mapping()])
        checks["integration_promotion_gate"] = promotion["selected_ids"] == ["strategy_contract"]

        compiled = SubmissionCompiler().compile(CompilationSpec(
            source=ROOT / "baby_solver.py",
            submission_dir=temporary / "submission",
            manifest_path=temporary / "build_manifest.json",
        ))
        checks["single_file_compiler"] = (
            compiled["output"]["layout_valid"]
            and compiled["output"]["ast_valid"]
            and (temporary / "submission" / "solver.py").is_file()
            and len(list((temporary / "submission").iterdir())) == 1
        )

    output = {"passed": all(checks.values()), "checks": checks}
    print(json.dumps(output, ensure_ascii=False, sort_keys=True))
    return 0 if output["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
