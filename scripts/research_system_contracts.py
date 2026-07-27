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
from research_system.executor import MechanicalExecutor  # noqa: E402
from research_system.experience import ExperienceStore  # noqa: E402
from research_system.finite_models import (  # noqa: E402
    BundleModelConfig,
    SkewProductConfig,
    affine_fiber_library,
    affine_rectangular_library,
    analyze_congruence_decompositions,
    bundle_counterexample_search,
    skew_product_counterexample_search,
)
from research_system.integration import IntegrationCatalog  # noqa: E402
from research_system.infinite_models import (  # noqa: E402
    assemble_infinite_model_plan,
    merge_infinite_model_patch,
)
from research_system.obligations import ObligationGraph, infer_approach_family  # noqa: E402
from research_system.orchestrator import ResearchEpisodeRunner, compact_mechanical_feedback  # noqa: E402
from research_system.planner import (  # noqa: E402
    ContextAugmentingPlanner,
    FeedbackRepairPlanner,
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
from research_system.teacher import (  # noqa: E402
    TeacherSearchConfig,
    TeacherStudentSearch,
)


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
            "helper_chain_portfolio",
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
    original_judge_true_attributed = baby_solver.judge_true_attributed
    judged_forward_routes: list[str] = []
    try:
        accept_route = saturation_bodies[1][0] if len(saturation_bodies) > 1 else saturation_bodies[0][0]

        def fake_judge_true_attributed(route, body, **kwargs):
            del body, kwargs
            judged_forward_routes.append(route)
            return {"status": "accepted" if route.endswith(accept_route) else "incorrect"}

        baby_solver.judge_true_attributed = fake_judge_true_attributed
        fs_body, fs_state = baby_solver.run_tool_call_detailed(
            {"kind": "tool_call", "tool": "forward_saturation", "target": "goal"},
            replacement_h,
            replacement_g,
            verify_candidates=True,
        )
    finally:
        baby_solver.judge_true_attributed = original_judge_true_attributed
    checks["forward_saturation_tool_verifies_cheapest_first"] = (
        fs_body is not None
        and fs_state is not None
        and fs_state.get("status") == "proved"
        and fs_state.get("accepted_route") == accept_route
        and len(judged_forward_routes) == 2
        and fs_state.get("already_judged_accepted") is True
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
    proj_l_h = baby_solver.parse_equation("x = x ◇ ((y ◇ z) ◇ (x ◇ y))")
    proj_l_g = baby_solver.parse_equation("x = x ◇ ((y ◇ y) ◇ (z ◇ y))")
    projection_contract_budget = 8
    proj_l_body, proj_l_state = baby_solver.standard_aux_superposition_attempt(
        proj_l_h,
        proj_l_g,
        {"lemmas": ["const", "proj_l", "proj_r", "rowconst"], "budget": projection_contract_budget},
    )
    proj_r_h = baby_solver.parse_equation("x = (y ◇ ((z ◇ x) ◇ z)) ◇ x")
    proj_r_g = baby_solver.parse_equation("x = ((y ◇ z) ◇ w) ◇ (w ◇ x)")
    proj_r_body, proj_r_state = baby_solver.standard_aux_superposition_attempt(
        proj_r_h,
        proj_r_g,
        {"lemmas": ["const", "proj_l", "proj_r", "rowconst"], "budget": projection_contract_budget},
    )
    checks["standard_aux_projection_focus"] = (
        proj_l_body is not None
        and proj_l_state.get("used_aux") == "proj_l"
        and proj_l_state.get("attempts", [{}])[0].get("kind") == "proj_l"
        and proj_r_body is not None
        and proj_r_state.get("used_aux") == "proj_r"
        and proj_r_state.get("attempts", [{}])[0].get("kind") == "proj_r"
    )
    chain_h = baby_solver.parse_equation("x = (y ◇ (x ◇ x)) ◇ (z ◇ x)")
    chain_g = baby_solver.parse_equation("x = y ◇ (((x ◇ z) ◇ z) ◇ x)")
    chain_body, chain_state = baby_solver.helper_chain_portfolio_attempt(
        chain_h,
        chain_g,
        {"chains": ["generic_right_square_absorption"], "budget": 12},
        budget=12,
    )
    checks["helper_chain_portfolio_hard3_0204"] = (
        chain_body is not None
        and chain_state.get("winning_chain") == "generic_right_square_absorption"
        and [row.get("name") for row in chain_state.get("proved_lemmas", [])]
        == ["square_absorb", "right_square"]
    )
    nested_chain_h = baby_solver.parse_equation("x = (y ◇ (z ◇ x)) ◇ (w ◇ x)")
    nested_chain_g = baby_solver.parse_equation("x = ((x ◇ y) ◇ y) ◇ (y ◇ x)")
    nested_body, nested_state = baby_solver.helper_chain_portfolio_attempt(
        nested_chain_h,
        nested_chain_g,
        {"chains": ["nested_tail_absorption"], "budget": 36},
        budget=36,
    )
    checks["helper_chain_portfolio_hard3_0210"] = (
        nested_body is not None
        and nested_state.get("winning_chain") == "nested_tail_absorption"
        and [row.get("name") for row in nested_state.get("proved_lemmas", [])]
        == ["nested_absorb", "tail_any"]
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
    family_h = baby_solver.parse_equation("x ◇ y = x")
    family_g = baby_solver.parse_equation("x ◇ y = y")
    family_action, family_adapter = baby_solver.normalize_llm_action({
        "kind": "symbolic_model",
        "carrier_size": 3,
        "default": {"kind": "left"},
        "budget": 2,
    })
    assert family_action is not None
    family_found, family_state = baby_solver.false_model_family_attempt(
        family_h,
        family_g,
        family_action,
    )
    near_found, near_state = baby_solver.false_model_family_attempt(
        family_h,
        family_g,
        {
            "kind": "false_model_family",
            "carrier_size": 3,
            "default": {"kind": "constant", "params": [0]},
            "budget": 2,
        },
    )
    unsafe_found, unsafe_state = baby_solver.false_model_family_attempt(
        family_h,
        family_g,
        {
            "kind": "false_model_family",
            "carrier_size": 3,
            "default": {"kind": "left"},
            "rules": [{"when": "i == j", "value": "__import__('os').system('true')"}],
            "budget": 2,
        },
    )
    invalid_rules_found, invalid_rules_state = baby_solver.false_model_family_attempt(
        family_h,
        family_g,
        {
            "kind": "false_model_family",
            "carrier_size": 3,
            "default": {"kind": "left"},
            "rules": {"when": {"kind": "diagonal"}, "value": 0},
            "budget": 2,
        },
    )
    repaired_alias_found, repaired_alias_state = baby_solver.false_model_family_attempt(
        family_h,
        family_g,
        {
            "kind": "false_model_family",
            "carrier_size": 2,
            "default": {"kind": "left"},
            "rules": [
                {
                    "when": {"kind": "pair", "left": 0, "right": 1},
                    "value": 0,
                },
                {
                    "when": {"kind": "left_eq", "value": 1},
                    "value": "i",
                },
                {
                    "when": {"kind": "diagonal", "i": 1},
                    "value": 1,
                },
            ],
            "budget": 2,
        },
    )
    family_gate = baby_solver.capability_gate_state(
        "false_model_family",
        {"disabled": ["primitive:symbolic_family_evaluator"]},
    )
    invariant_rows = baby_solver.symbolic_invariant_report(family_h, family_g)
    checks["finite_symbolic_family_contract"] = (
        family_action.get("kind") == "tool_call"
        and family_action.get("tool") == "false_model_family"
        and family_adapter is None
        and family_found is not None
        and family_found[0] == 3
        and baby_solver.is_counterexample(family_h, family_g, family_found[1])
        and family_state.get("status") == "found"
        and family_state.get("h_profile", {}).get("complete") is True
        and family_state.get("g_profile", {}).get("failures_observed", 0) > 0
        and invariant_rows[0].get("family") == "left_projection"
        and invariant_rows[0].get("separates_goal") is True
        and invariant_rows[0].get("action", {}).get("tool") is None
        and invariant_rows[0].get("action", {}).get("kind") == "false_model_family"
    )
    checks["finite_symbolic_family_repair_feedback"] = (
        near_found is None
        and near_state.get("status") == "h_violated"
        and near_state.get("repair_class") == "repair_h_preserve_g"
        and bool(near_state.get("h_profile", {}).get("examples"))
        and bool(near_state.get("g_profile", {}).get("examples"))
        and unsafe_found is None
        and unsafe_state.get("status") == "invalid_family"
        and invalid_rules_found is None
        and invalid_rules_state.get("status") == "invalid_family"
        and repaired_alias_found is not None
        and len(
            repaired_alias_state.get("family_summary", {}).get("schema_repairs") or []
        ) == 3
        and family_gate is not None
        and family_gate.get("status") == "withheld_for_curriculum"
    )
    skew_h = baby_solver.parse_equation("x = (y ◇ y) ◇ (x ◇ (y ◇ x))")
    skew_g = baby_solver.parse_equation("x ◇ y = (x ◇ (x ◇ x)) ◇ y")
    skew_status, skew_table, skew_state = skew_product_counterexample_search(
        skew_h,
        skew_g,
        SkewProductConfig(
            control_size=2,
            fiber_size=3,
            time_budget=5,
            max_iterations=32,
            workers=2,
        ),
    )
    skew_normalized, skew_adapter = MechanicalExecutor.normalize({
        "kind": "skew_product_search",
        "quotient_size": 2,
        "fiber_size": 3,
        "budget": 5,
    })
    checks["skew_product_constructor_contract"] = (
        len(affine_fiber_library(3)) == 27
        and skew_normalized is not None
        and skew_normalized.get("kind") == "skew_model_search"
        and skew_normalized.get("control_size") == 2
        and skew_adapter is None
        and (
            (
                skew_status == "found"
                and skew_table is not None
                and baby_solver.is_counterexample(skew_h, skew_g, skew_table)
                and skew_state.get("status") == "verified_countermodel"
                and skew_state.get("parameters", {}).get("parameter_count") == 8
            )
            or (
                skew_status == "unavailable"
                and skew_table is None
                and skew_state.get("status") == "unavailable"
            )
        )
    )
    packed_skew_h = baby_solver.parse_equation(
        "x = ((x ◇ x) ◇ (y ◇ z)) ◇ y"
    )
    packed_skew_g = baby_solver.parse_equation(
        "x = ((x ◇ (y ◇ x)) ◇ x) ◇ y"
    )
    packed_skew_found, packed_skew_state = baby_solver.false_model_search_detailed(
        packed_skew_h,
        packed_skew_g,
        {
            "template": "skew_product",
            "routes": ["skew_product:2x3"],
            "budget": 4,
        },
        4,
    )
    packed_small_skew_found, packed_small_skew_state = (
        baby_solver.false_model_search_detailed(
            packed_skew_h,
            packed_skew_g,
            {
                "routes": ["skew_product:2x2"],
                "budget": 4,
            },
            4,
        )
    )
    packed_cp_available = baby_solver._CP_SAT_AVAILABLE
    try:
        baby_solver._CP_SAT_AVAILABLE = False
        packed_pure_skew_found, packed_pure_skew_state = (
            baby_solver.false_model_search_detailed(
                packed_skew_h,
                packed_skew_g,
                {
                    "routes": ["skew_product:2x3"],
                    "budget": 4,
                },
                4,
            )
        )
    finally:
        baby_solver._CP_SAT_AVAILABLE = packed_cp_available
    packed_pure_trial = packed_pure_skew_state.get("trials", [{}])[-1]
    checks["packed_skew_product_route_contract"] = (
        packed_skew_found is not None
        and len(packed_skew_found[1]) == 6
        and baby_solver.is_counterexample(
            packed_skew_h,
            packed_skew_g,
            packed_skew_found[1],
        )
        and packed_skew_state.get("status") == "found"
        and packed_skew_state.get("witness_style")
        == "quotient_fiber_skew_product"
        and packed_small_skew_found is None
        and packed_small_skew_state.get("trials", [{}])[-1].get("status")
        == "family_infeasible"
        and packed_small_skew_state.get("recommended_next_call", {}).get(
            "routes"
        )
        == ["skew_product:2x3"]
        and packed_pure_skew_found is not None
        and baby_solver.is_counterexample(
            packed_skew_h,
            packed_skew_g,
            packed_pure_skew_found[1],
        )
        and packed_pure_trial.get("backend")
        == "pure_python_enumeration"
    )
    bundle_h = baby_solver.parse_equation(
        "x = ((x ◇ (y ◇ z)) ◇ z) ◇ x"
    )
    bundle_g = baby_solver.parse_equation(
        "x = ((x ◇ x) ◇ (y ◇ y)) ◇ x"
    )
    bundle_status, bundle_table, bundle_state = bundle_counterexample_search(
        bundle_h,
        bundle_g,
        BundleModelConfig(
            fiber_sizes=(4, 2),
            max_patches=6,
            time_budget=6,
            max_iterations=160,
            workers=2,
        ),
    )
    bundle_normalized, bundle_adapter = MechanicalExecutor.normalize({
        "kind": "fiber_bundle_search",
        "block_sizes": [4, 2],
        "max_patches": 6,
        "budget": 6,
    })
    checks["bundle_model_constructor_contract"] = (
        len(affine_rectangular_library(4, 2, 4)) == 64
        and bundle_normalized is not None
        and bundle_normalized.get("kind") == "bundle_model_search"
        and bundle_normalized.get("fiber_sizes") == (4, 2)
        and bundle_adapter is None
        and (
            (
                bundle_status == "found"
                and bundle_table is not None
                and baby_solver.is_counterexample(bundle_h, bundle_g, bundle_table)
                and bundle_state.get("status") == "verified_countermodel"
                and bundle_state.get("parameters", {}).get("patch_count") <= 6
            )
            or (
                bundle_status == "unavailable"
                and bundle_table is None
                and bundle_state.get("status") == "unavailable"
            )
        )
    )
    hard2_0125_known_table = [
        [0, 5, 2, 3, 3, 3],
        [4, 1, 1, 4, 4, 4],
        [0, 2, 2, 3, 0, 5],
        [0, 2, 2, 3, 3, 3],
        [4, 1, 4, 4, 4, 4],
        [5, 2, 2, 5, 5, 5],
    ]
    decomposition = analyze_congruence_decompositions(hard2_0125_known_table)
    checks["congruence_decomposition_contract"] = (
        decomposition.get("status") == "complete"
        and decomposition.get("decomposition_count") == 1
        and decomposition["decompositions"][0]["block_sizes"] == [4, 2]
        and decomposition["decompositions"][0]["quotient_table"]
        == [[0, 0], [1, 1]]
        and not decomposition["decompositions"][0]["equal_fibers"]
    )
    original_call_llm = baby_solver.call_llm
    original_judge_infinite = baby_solver.judge_infinite_model_artifact_attributed
    infinite_contexts: list[dict] = []
    infinite_judges: list[str] = []
    infinite_responses = [
        {
            "kind": "infinite_model",
            "code": "import JudgeProblem\n\ndef submission : Goal := by\n  exact first_attempt",
        },
        {
            "kind": "infinite_model",
            "code": "import JudgeProblem\n\ndef submission : Goal := by\n  exact repaired_attempt",
        },
    ]
    try:
        def fake_call_llm(context):
            infinite_contexts.append(context)
            response = infinite_responses[min(len(infinite_contexts) - 1, 1)]
            return {"response": json.dumps(response)}

        def fake_judge_infinite(route, code, **kwargs):
            del route, kwargs
            infinite_judges.append(code)
            if len(infinite_judges) == 1:
                return {"status": "incorrect", "stderr": "unknown identifier first_attempt"}
            return {"status": "accepted"}

        baby_solver.call_llm = fake_call_llm
        baby_solver.judge_infinite_model_artifact_attributed = fake_judge_infinite
        infinite_status = baby_solver.try_llm_collaboration(
            baby_solver.parse_equation("x = x"),
            baby_solver.parse_equation("x = y"),
            30,
            max_rounds=3,
            collaboration_goal="repair a complete infinite model",
            prefer_false=True,
            semantic_context={
                "semantic_class": "contract_infinite",
                "general_status": "false",
                "finite_status": "true",
                "certificate_class": "infinite_model",
            },
            allow_infinite_model_artifacts=True,
        )
    finally:
        baby_solver.call_llm = original_call_llm
        baby_solver.judge_infinite_model_artifact_attributed = original_judge_infinite
    checks["infinite_model_multi_round_repair"] = (
        infinite_status == "accepted_false_infinite_model_llm"
        and len(infinite_contexts) == 2
        and len(infinite_judges) == 2
        and "judge_rejected_infinite_model" in infinite_contexts[1].get("mechanical_feedback", "")
        and "20,000-byte false-certificate envelope" in baby_solver.PROMPT
    )
    structured_fixture = json.loads(
        (
            ROOT
            / "data"
            / "semantics"
            / "austin_3994_3588_infinite_model_plan.json"
        ).read_text(encoding="utf-8")
    )
    structured_code, structured_state = assemble_infinite_model_plan(structured_fixture)
    incomplete_code, incomplete_state = assemble_infinite_model_plan({
        "kind": "infinite_model_plan",
        "carrier": "ℕ",
        "operation": "fun x y ↦ x",
    })
    patched_fixture = merge_infinite_model_patch(
        structured_fixture,
        {
            "kind": "infinite_model_patch",
            "set": {"hypothesis_proof": "intro x y z\nexact repaired_marker"},
        },
    )
    noisy_fixture = dict(structured_fixture)
    noisy_fixture["hypothesis_proof"] = (
        "by\n"
        "  intro x y z\n"
        "  simp <;> omega"
    )
    noisy_code, noisy_state = assemble_infinite_model_plan(noisy_fixture)
    singleton_fixture = dict(structured_fixture)
    singleton_fixture["imports"] = "Mathlib.Tactic"
    singleton_fixture["setup"] = structured_fixture["setup"][0]
    singleton_code, singleton_state = assemble_infinite_model_plan(singleton_fixture)
    repairable_envelope = {
        "kind": "symbolic_model_plan",
        "representation": "infinite",
        "carrier": "Nat",
        "definitions": ["def op (x y : Nat) : Nat := x"],
        "setup": [
            "have helper (x : Nat) : op x x = x := by",
            "  rfl",
        ],
        "hypothesis_proof": "intro x y\nrfl",
        "counterexample_proof": "intro goal_holds\nexact False.elim (by contradiction)",
    }
    repaired_envelope, repaired_envelope_state = baby_solver.normalize_symbolic_model_plan(
        repairable_envelope
    )
    checks["structured_infinite_model_assembly"] = (
        structured_code is not None
        and structured_state.get("status") == "candidate_ready"
        and structured_state.get("part_count") == 6
        and "let magN : Magma (ℕ)" in structured_code
        and incomplete_code is None
        and set(incomplete_state.get("missing_parts") or [])
        == {"hypothesis_proof", "counterexample_proof"}
        and patched_fixture.get("operation") == structured_fixture.get("operation")
        and "repaired_marker" in patched_fixture.get("hypothesis_proof", "")
        and noisy_code is not None
        and {
            row.get("repair")
            for row in noisy_state.get("syntax_repairs") or []
        }
        == {
            "removed_redundant_outer_by",
            "dedented_following_tactics_by_2",
        }
        and singleton_code is not None
        and {
            row.get("repair")
            for row in singleton_state.get("schema_repairs") or []
        }
        == {
            "wrapped_single_import_as_list",
            "wrapped_single_setup_fragment_as_list",
        }
        and repaired_envelope is not None
        and repaired_envelope.get("operation") == "op"
        and repaired_envelope.get("definitions") == [
            "let op (x y : Nat) : Nat := x"
        ]
        and len(repaired_envelope.get("setup") or []) == 1
        and {
            row.get("repair")
            for row in repaired_envelope_state.get("schema_repairs") or []
        }
        == {
            "merged_dangling_tactic_fragment",
            "inferred_operation_from_local_op_definition",
        }
    )
    parity_fixture = json.loads(
        (
            ROOT
            / "data"
            / "semantics"
            / "hard2_0027_modified_parity_model_plan.json"
        ).read_text(encoding="utf-8")
    )
    parity_code, parity_state = assemble_infinite_model_plan(parity_fixture)
    definition_span = (parity_state.get("line_ranges") or {}).get("definitions", [{}])[0]
    definition_feedback = baby_solver.symbolic_model_judge_feedback(
        {
            "message": (
                f"Submission.lean:{definition_span.get('start', 1)}:7: "
                "error: unknown identifier 'paritty'"
            ),
        },
        parity_state,
    )
    indexed_patch = merge_infinite_model_patch(
        parity_fixture,
        {
            "kind": "symbolic_model_patch",
            "set": {"definitions[1]": "let op (x y : Nat) := Nat.succ y"},
        },
    )
    checks["symbolic_pre_model_definitions"] = (
        parity_code is not None
        and parity_state.get("status") == "candidate_ready"
        and (parity_state.get("assembly") or {}).get("definition_count") == 2
        and "let parity : Nat → Bool" in parity_code
        and "let op (x y : Nat)" in parity_code
        and definition_feedback.get("failed_parts") == ["definitions[0]"]
        and "definitions" not in definition_feedback.get("preserve_parts", [])
        and "operation" in definition_feedback.get("preserve_parts", [])
        and indexed_patch.get("definitions", [None, None])[1]
        == "let op (x y : Nat) := Nat.succ y"
    )
    large_finite_code, large_finite_state = assemble_infinite_model_plan({
        "kind": "symbolic_model_plan",
        "representation": "symbolic_finite",
        "model_name": "model",
        "imports": ["Mathlib.Tactic"],
        "carrier": "Fin 257",
        "definitions": [],
        "operation": "fun x _ => x",
        "setup": [],
        "hypothesis_proof": "intro x y\nrfl",
        "counterexample_proof": (
            "intro goal_holds\n"
            "have h := goal_holds (0 : Fin 257) (1 : Fin 257)\n"
            "change (0 : Fin 257) = 1 at h\n"
            "exact Fin.zero_ne_one h"
        ),
    })
    checks["large_symbolic_finite_without_table"] = (
        large_finite_state.get("status") == "candidate_ready"
        and large_finite_code is not None
        and "Magma (Fin 257)" in large_finite_code
        and "counterexample_table" not in large_finite_code
    )
    ray_h = baby_solver.parse_equation(
        "x = y ◇ ((z ◇ (y ◇ y)) ◇ x)"
    )
    ray_g = baby_solver.parse_equation(
        "x = (y ◇ z) ◇ ((x ◇ z) ◇ x)"
    )
    ray_code, ray_state = baby_solver.residue_ray_countermodel_attempt(
        ray_h,
        ray_g,
        {
            "kind": "tool_call",
            "tool": "residue_ray_countermodel",
            "moduli": [2],
            "a_values": [-1, 0, 1],
            "b_values": [-1, 0, 1],
            "c_values": [-1, 0, 1],
            "candidate_cap": 2000,
            "budget": 2,
        },
    )
    ray_alpha_code, ray_alpha_state = baby_solver.residue_ray_countermodel_attempt(
        baby_solver.parse_equation("b ◇ ((c ◇ (b ◇ b)) ◇ a) = a"),
        baby_solver.parse_equation("a = (b ◇ c) ◇ ((a ◇ c) ◇ a)"),
        {
            "kind": "tool_call",
            "tool": "residue_ray_countermodel",
            "moduli": [2],
            "a_values": [-1, 0, 1],
            "b_values": [-1, 0, 1],
            "c_values": [-1, 0, 1],
            "candidate_cap": 2000,
            "budget": 2,
        },
    )
    checks["equation_driven_residue_ray_certificate"] = (
        ray_code is not None
        and ray_state.get("status") == "candidate_ready"
        and (ray_state.get("candidate") or {}).get("same") == [0, 1, 1]
        and (ray_state.get("candidate") or {}).get("different") == [0, 1, -1]
        and "Bool × Nat" in ray_code
        and ray_alpha_code is not None
        and ray_alpha_state.get("status") == "candidate_ready"
        and "    symm\n" in ray_alpha_code
    )
    checks["submission_has_no_exact_case_replay"] = not any(
        marker in solver_source
        for marker in (
            "hard2_0027",
            "(1167, 1763)",
            "VERIFIED_SYMBOLIC_MODEL_ARTIFACTS",
            "verified_symbolic_model_artifact",
        )
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
    repair_recommendation = {
        "kind": "bundle_model_search",
        "fiber_sizes": [4, 2],
        "max_patches": 6,
        "budget": 30,
    }
    repair_planner = FeedbackRepairPlanner(
        ScriptedPlanner([
            {
                "kind": "bundle_model_search",
                "fiber_sizes": [3, 2],
                "max_patches": 4,
            },
            repair_recommendation,
        ]),
        max_corrections=1,
    )
    repaired_action = repair_planner.next_action({
        "recent_observations": [{
            "mechanical_status": "family_infeasible",
            "suggested_next_actions": [repair_recommendation],
        }],
    })
    checks["feedback_repair_planner"] = (
        repaired_action == repair_recommendation
        and repair_planner.last_trace is not None
        and repair_planner.last_trace.get("correction_count") == 1
        and repair_planner.last_trace.get("matched_primary_recommendation") is True
    )
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

    class TeacherExecutor:
        name = "fake_teacher_executor"

        @staticmethod
        def normalize(action: dict) -> tuple[dict, None]:
            return action, None

        @staticmethod
        def planner_diagnostics(problem, *, semantics=None, max_carrier=4) -> dict:
            del problem, semantics, max_carrier
            return {
                "symbolic_invariant_report": [{"family": "left_projection", "separates": True}],
                "finite_countermodel_search_allowed": True,
            }

        def execute(self, problem, action, **kwargs) -> ExecutionResult:
            del problem, kwargs
            candidate = action.get("candidate_id")
            if candidate == "winner":
                return ExecutionResult(
                    status="candidate_ready",
                    submitted_action=action,
                    finite_table=[[0, 0], [1, 1]],
                    state={
                        "kind": "FalseModelFamilyState",
                        "status": "found",
                        "repair_class": "verified_countermodel",
                    },
                )
            return ExecutionResult(
                status="mechanical_stuck",
                submitted_action=action,
                state={
                    "kind": "FalseModelFamilyState",
                    "status": "h_violated",
                    "repair_class": "repair_h_preserve_g",
                    "h_profile": {"failures_observed": 3},
                    "g_profile": {"failures_observed": 1},
                    "need_hint": "repair the three H-violating cells",
                },
            )

    class TeacherVerifier:
        def verify(self, problem, execution, *, profile="competition") -> VerificationRecord:
            del problem, execution
            return VerificationRecord(
                status="accepted",
                accepted=True,
                verdict="false",
                profile=profile,
            )

    teacher_case = CurriculumCase(
        case_id="contract_teacher_student",
        problem=ProblemSpec(
            id="contract_teacher_student",
            eq1_id=7,
            eq2_id=8,
            equation1="x ◇ y = x",
            equation2="x ◇ y = y",
            answer=False,
        ),
        actions=(),
        expected_verdict="false",
        max_rounds=1,
    )
    near_action = {
        "kind": "false_model_family",
        "candidate_id": "near",
        "carrier_size": 2,
        "default": {"kind": "constant", "params": [0]},
    }
    winning_action = {
        "kind": "false_model_family",
        "candidate_id": "winner",
        "carrier_size": 2,
        "default": {"kind": "left"},
    }
    teacher_runner = ResearchEpisodeRunner(
        semantics=semantics,
        executor=TeacherExecutor(),
        verifier=TeacherVerifier(),
    )
    teacher_config = TeacherSearchConfig(
        beam_width=1,
        proposals_per_branch=2,
        max_depth=1,
        branch_rounds=1,
        student_rounds=1,
        exploration_fraction=0,
    )

    def student_factory(lesson):
        return ScriptedPlanner(
            [winning_action if lesson is not None else near_action],
            name="contract_student",
        )

    teacher_report = TeacherStudentSearch(
        teacher_runner,
        ScriptedPlanner([near_action, winning_action], name="contract_teacher"),
        config=teacher_config,
        student_planner_factory=student_factory,
    ).run(teacher_case)
    checks["teacher_beam_mechanical_scoring"] = (
        teacher_report.get("outcome") == "student_replay"
        and teacher_report["teacher"]["generations"][0]["candidate_count"] == 2
        and teacher_report["teacher"]["winner"]["action"].get("candidate_id") == "winner"
        and teacher_report["mechanical_diagnostics"]["finite_countermodel_search_allowed"]
    )
    checks["teacher_student_load_bearing_promotion"] = (
        teacher_report["student"]["load_bearing"] is True
        and teacher_report["student"]["no_lesson"]["accepted"] is False
        and teacher_report["student"]["with_lesson"]["accepted"] is True
        and teacher_report["minimization"]["mechanical_replay_episode"]["accepted"] is True
        and teacher_report["artifact"]["kind"] == "teacher_student_lesson"
    )
    unsolved_report = TeacherStudentSearch(
        teacher_runner,
        ScriptedPlanner([near_action], name="contract_teacher_unsolved"),
        config=TeacherSearchConfig(
            beam_width=1,
            proposals_per_branch=1,
            max_depth=1,
            branch_rounds=1,
            student_rounds=1,
        ),
    ).run(teacher_case)
    checks["teacher_unsolved_outcome"] = (
        unsolved_report.get("outcome") == "teacher_unsolved"
        and unsolved_report.get("artifact") is None
        and len(unsolved_report.get("resume_state", {}).get("beam") or []) == 1
    )
    resumed_teacher_contexts: list[dict] = []

    def resumed_teacher_plan(context):
        resumed_teacher_contexts.append(context)
        return {**near_action, "candidate_id": "near_resumed"}

    resumed_teacher_report = TeacherStudentSearch(
        teacher_runner,
        FunctionPlanner(resumed_teacher_plan, name="contract_resumed_teacher"),
        config=TeacherSearchConfig(
            beam_width=1,
            proposals_per_branch=1,
            max_depth=2,
            branch_rounds=1,
            student_rounds=1,
            focus="finite_symbolic",
        ),
    ).run(teacher_case, resume_from=unsolved_report)
    checks["teacher_beam_resume"] = (
        resumed_teacher_report.get("outcome") == "teacher_unsolved"
        and len(resumed_teacher_report["teacher"]["generations"]) == 2
        and resumed_teacher_contexts[0]["teacher_search"]["depth"] == 2
        and resumed_teacher_contexts[0]["teacher_search"]["parent_action"].get("candidate_id")
        == "near"
    )

    def failing_student_factory(lesson):
        del lesson
        return ScriptedPlanner([near_action], name="contract_failing_student")

    non_distillable_report = TeacherStudentSearch(
        teacher_runner,
        ScriptedPlanner([winning_action], name="contract_teacher_only"),
        config=TeacherSearchConfig(
            beam_width=1,
            proposals_per_branch=1,
            max_depth=1,
            branch_rounds=1,
            student_rounds=1,
        ),
        student_planner_factory=failing_student_factory,
    ).run(teacher_case)
    checks["teacher_solved_not_distillable_outcome"] = (
        non_distillable_report.get("outcome") == "teacher_solved_not_distillable"
        and non_distillable_report.get("artifact") is None
    )
    repair_contexts: list[dict] = []

    def cumulative_repair_plan(context):
        repair_contexts.append(context)
        return {
            **near_action,
            "candidate_id": f"near_depth_{context['teacher_search']['depth']}",
        }

    TeacherStudentSearch(
        teacher_runner,
        FunctionPlanner(cumulative_repair_plan, name="contract_cumulative_repair"),
        config=TeacherSearchConfig(
            beam_width=1,
            proposals_per_branch=1,
            max_depth=2,
            branch_rounds=1,
            student_rounds=1,
            focus="finite_symbolic",
        ),
    ).run(teacher_case)
    checks["teacher_parent_action_feedback"] = (
        len(repair_contexts) == 2
        and repair_contexts[1]["teacher_search"]["parent_action"].get("candidate_id")
        == "near_depth_1"
        and repair_contexts[1]["recent_observations"][0].get("repair_class")
        == "repair_h_preserve_g"
        and repair_contexts[1]["recent_observations"][0]
        .get("h_profile", {})
        .get("failures_observed")
        == 3
    )

    class InfiniteRepairVerifier:
        def verify(self, problem, execution, *, profile="research") -> VerificationRecord:
            del problem
            repaired = bool(
                execution.infinite_code
                and "repaired_marker" in execution.infinite_code
            )
            return VerificationRecord(
                status="accepted" if repaired else "incorrect",
                accepted=repaired,
                verdict="false",
                profile=profile,
                message=None if repaired else "structured proof failed",
                error_code=None if repaired else "lean_elaboration_error",
                details={
                    "stderr": (
                        ""
                        if repaired
                        else "unknown identifier first_attempt in hypothesis_proof"
                    ),
                },
            )

    infinite_repair_contexts: list[dict] = []
    first_structured_plan = {
        "kind": "infinite_model_plan",
        "model_name": "model",
        "carrier": "ℕ",
        "operation": "fun x y ↦ x",
        "setup": [],
        "hypothesis_proof": "intro x y z\nexact first_attempt",
        "counterexample_proof": "exact first_counterexample",
    }

    def infinite_repair_plan(context):
        infinite_repair_contexts.append(context)
        if context["teacher_search"]["depth"] == 1:
            return first_structured_plan
        return {
            "kind": "infinite_model_patch",
            "set": {
                "hypothesis_proof": "intro x y z\nexact repaired_marker",
            },
        }

    infinite_repair_case = CurriculumCase(
        case_id="contract_structured_infinite_repair",
        problem=ProblemSpec(
            id="contract_structured_infinite_repair",
            eq1_id=1167,
            eq2_id=1763,
            equation1="x = x",
            equation2="x = x",
            answer=False,
        ),
        actions=(),
        expected_verdict="false",
        verification_profile="research",
        max_rounds=2,
    )
    infinite_repair_runner = ResearchEpisodeRunner(
        semantics=semantics,
        executor=MechanicalExecutor(),
        verifier=InfiniteRepairVerifier(),
    )
    infinite_repair_report = TeacherStudentSearch(
        infinite_repair_runner,
        FunctionPlanner(infinite_repair_plan, name="contract_infinite_repair"),
        config=TeacherSearchConfig(
            beam_width=1,
            proposals_per_branch=1,
            max_depth=2,
            branch_rounds=1,
            student_rounds=2,
            focus="infinite_model",
        ),
    ).run(infinite_repair_case)
    repaired_action = infinite_repair_report["teacher"]["winner"]["action"]
    checks["structured_infinite_model_repair_loop"] = (
        infinite_repair_report.get("outcome") == "teacher_solved_not_distillable"
        and len(infinite_repair_contexts) == 2
        and "unknown identifier first_attempt"
        in infinite_repair_contexts[1]["recent_observations"][0]
        .get("verification", {})
        .get("details", {})
        .get("stderr", "")
        and repaired_action.get("operation") == first_structured_plan.get("operation")
        and "repaired_marker" in repaired_action.get("hypothesis_proof", "")
        and infinite_repair_report["minimization"]["minimized_action_count"] == 1
    )
    augmented_contexts: list[dict] = []
    augmented = ContextAugmentingPlanner(
        FunctionPlanner(
            lambda context: augmented_contexts.append(context) or near_action,
            name="contract_context_sink",
        ),
        {"teacher_lesson": {"kind": "verified_teacher_trajectory"}},
    )
    augmented.next_action({"problem": teacher_case.problem.to_mapping()})
    checks["teacher_lesson_context_adapter"] = (
        augmented_contexts[0]["teacher_lesson"]["kind"] == "verified_teacher_trajectory"
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
    compact = compact_mechanical_feedback(
        {
            "kind": "SearchState",
            "status": "family_infeasible",
            "need_hint": "propose a bridge",
            "stderr": "x" * 10000,
            "goal_search_state": {
                "target": "x = y",
                "closest_pairs": [{"left": "x", "right": "y"}],
            },
            "budget_allocation": {"policy_id": "contract", "events": [{"event": "grant"}]},
            "repair_class": "repair_h_preserve_g",
            "family_summary": {"carrier_size": 3, "rule_count": 2},
            "h_profile": {
                "failures_observed": 2,
                "examples": [{"env": {"x": 0}, "cells": [[0, 1]]}],
            },
            "g_profile": {"failures_observed": 1},
            "errors": [{"code": "contract_schema_error"}],
        },
        execution_status="mechanical_stuck",
    )
    checks["compact_system2_feedback"] = (
        compact.get("need_hint") == "propose a bridge"
        and compact.get("status") == "mechanical_stuck"
        and compact.get("mechanical_status") == "family_infeasible"
        and "stderr" not in compact
        and compact.get("goal_search", {}).get("target") == "x = y"
        and compact.get("budget_allocation", {}).get("policy_id") == "contract"
        and compact.get("repair_class") == "repair_h_preserve_g"
        and compact.get("h_profile", {}).get("failures_observed") == 2
        and compact.get("g_profile", {}).get("failures_observed") == 1
        and compact.get("errors", [{}])[0].get("code") == "contract_schema_error"
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
