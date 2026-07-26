"""Trusted mechanical execution adapter over the current packed solver engines."""

from __future__ import annotations

import time
from typing import Any

import baby_solver

from .protocol import ExecutionResult, ProblemSpec, SemanticRecord
from .infinite_models import (
    assemble_infinite_model_plan,
    is_infinite_model_patch,
    is_infinite_model_plan,
)


class MechanicalExecutor:
    name = "baby_solver_adapter_v1"

    def __init__(self, *, budget_policy: dict[str, Any] | None = None):
        self.budget_policy = (
            baby_solver.MidpointBudgetPolicy.from_mapping(
                budget_policy,
                candidate_count=5,
            ).to_mapping()
            if budget_policy is not None
            else None
        )

    @staticmethod
    def normalize(action: dict[str, Any]) -> tuple[dict[str, Any] | None, dict[str, Any] | None]:
        if is_infinite_model_plan(action) or is_infinite_model_patch(action):
            return dict(action), None
        return baby_solver.normalize_llm_action(action)

    @staticmethod
    def planner_diagnostics(
        problem: ProblemSpec,
        *,
        semantics: SemanticRecord | None = None,
        max_carrier: int = 4,
    ) -> dict[str, Any]:
        """Expose cheap machine-computed clues without trusting a verdict."""
        h_eq = baby_solver.parse_equation(problem.equation1)
        g_eq = baby_solver.parse_equation(problem.equation2)
        semantic_context = semantics.to_mapping() if semantics is not None else None
        finite_allowed = (
            baby_solver.finite_countermodel_search_allowed(semantic_context)
            if semantic_context
            else True
        )
        diagnostics: dict[str, Any] = {
            "symbolic_invariant_report": baby_solver.symbolic_invariant_report(h_eq, g_eq),
            "finite_countermodel_search_allowed": finite_allowed,
        }
        if not finite_allowed:
            return diagnostics

        size_probe = []
        excluded_prefix = 1
        probe_budgets = {2: 0.8, 3: 0.35, 4: 0.45, 5: 30.0}
        for n in range(2, max(2, min(5, int(max_carrier))) + 1):
            budget = probe_budgets[n]
            status, table, meta = baby_solver.propagation_model_finder(
                h_eq,
                g_eq,
                n,
                time_budget=budget,
                node_cap=8_000_000 if n >= 5 else 1_000_000,
            )
            if table is not None:
                public_status = "countermodel_found"
            elif status == "none":
                public_status = "exhausted_no_countermodel"
                if n == excluded_prefix + 1:
                    excluded_prefix = n
            else:
                public_status = "unknown_budget"
            size_probe.append({
                "carrier_size": n,
                "status": public_status,
                "nodes": meta.get("nodes"),
                "forced_assignments": meta.get("forced_assignments"),
                "contradictions": meta.get("contradictions"),
            })
        diagnostics["finite_size_probe"] = size_probe
        if excluded_prefix >= 2:
            diagnostics["minimum_unexcluded_carrier_size"] = excluded_prefix + 1
        return diagnostics

    def execute(
        self,
        problem: ProblemSpec,
        action: dict[str, Any],
        *,
        capability_mask: Any = None,
        semantics: SemanticRecord | None = None,
        action_is_normalized: bool = False,
        adapter_state: dict[str, Any] | None = None,
    ) -> ExecutionResult:
        started = time.monotonic()
        h_eq = baby_solver.parse_equation(problem.equation1)
        g_eq = baby_solver.parse_equation(problem.equation2)
        normalized = action if action_is_normalized else None
        if not action_is_normalized:
            normalized, adapter_state = self.normalize(action)
        if normalized is None:
            return ExecutionResult(
                status="adapter_rejected",
                state=adapter_state or {},
                adapter_state=adapter_state,
                seconds=time.monotonic() - started,
            )
        if (
            self.budget_policy is not None
            and baby_solver.is_hint_payload(normalized)
            and not isinstance(normalized.get("budget_policy"), dict)
        ):
            normalized = dict(normalized)
            normalized["budget_policy"] = dict(self.budget_policy)
        semantic_context = semantics.to_mapping() if semantics is not None else None

        if is_infinite_model_plan(normalized):
            code, state = assemble_infinite_model_plan(normalized)
            return ExecutionResult(
                status="candidate_ready" if code else (
                    "artifact_rejected"
                    if state.get("status") == "invalid_plan"
                    else "mechanical_stuck"
                ),
                normalized_action=normalized,
                submitted_action=normalized,
                infinite_code=code,
                state=state,
                adapter_state=adapter_state,
                seconds=time.monotonic() - started,
            )

        if is_infinite_model_patch(normalized):
            return ExecutionResult(
                status="mechanical_stuck",
                normalized_action=normalized,
                submitted_action=normalized,
                state={
                    "kind": "InfiniteModelPlanState",
                    "status": "patch_without_parent",
                    "need_hint": (
                        "Apply this patch to a prior infinite_model_plan or return "
                        "a complete infinite_model_plan."
                    ),
                },
                adapter_state=adapter_state,
                seconds=time.monotonic() - started,
            )

        if baby_solver.is_infinite_model_payload(normalized):
            code, state = baby_solver.validate_infinite_model_payload(normalized)
            return ExecutionResult(
                status="candidate_ready" if code else "artifact_rejected",
                normalized_action=normalized,
                submitted_action=normalized,
                infinite_code=code,
                state=state,
                adapter_state=adapter_state,
                seconds=time.monotonic() - started,
            )

        if baby_solver.is_false_model_family_payload(normalized):
            gate = baby_solver.capability_gate_state("false_model_family", capability_mask)
            if gate is not None:
                return ExecutionResult(
                    status="capability_withheld",
                    normalized_action=normalized,
                    submitted_action=normalized,
                    state=gate,
                    adapter_state=adapter_state,
                    seconds=time.monotonic() - started,
                )
            if semantic_context and not baby_solver.finite_countermodel_search_allowed(semantic_context):
                state = baby_solver.semantic_status_state(semantic_context)
                return ExecutionResult(
                    status="artifact_rejected",
                    normalized_action=normalized,
                    submitted_action=normalized,
                    state=state,
                    adapter_state=adapter_state,
                    seconds=time.monotonic() - started,
                )
            found, state = baby_solver.false_model_family_attempt(h_eq, g_eq, normalized)
            table = found[1] if found is not None else None
            return ExecutionResult(
                status="candidate_ready" if table is not None else "mechanical_stuck",
                normalized_action=normalized,
                submitted_action=normalized,
                finite_table=table,
                state=state,
                adapter_state=adapter_state,
                seconds=time.monotonic() - started,
            )

        if normalized.get("kind") == "false_table" or normalized.get("verdict") == "false":
            table = normalized.get("counterexample_table") or normalized.get("table")
            valid = isinstance(table, list) and baby_solver.is_counterexample(h_eq, g_eq, table)
            state = baby_solver.protocol_state(
                "FiniteTableState",
                "counterexample_valid" if valid else "counterexample_invalid",
                "finite_table_validator",
                counterexample_size=len(table) if isinstance(table, list) else None,
            )
            return ExecutionResult(
                status="candidate_ready" if valid else "artifact_rejected",
                normalized_action=normalized,
                submitted_action=normalized,
                finite_table=table if valid else None,
                state=state,
                adapter_state=adapter_state,
                seconds=time.monotonic() - started,
            )

        if baby_solver.is_false_model_payload(normalized):
            gate = baby_solver.capability_gate_state("false_model_search", capability_mask)
            if gate is not None:
                return ExecutionResult(
                    status="capability_withheld",
                    normalized_action=normalized,
                    submitted_action=normalized,
                    state=gate,
                    adapter_state=adapter_state,
                    seconds=time.monotonic() - started,
                )
            found, state = baby_solver.false_model_search_detailed(
                h_eq,
                g_eq,
                normalized,
                float(normalized.get("budget") or 8.0),
                semantic_context=semantic_context,
            )
            table = found[1] if found and isinstance(found[1], list) else None
            return ExecutionResult(
                status="candidate_ready" if table is not None else "mechanical_stuck",
                normalized_action=normalized,
                submitted_action=normalized,
                finite_table=table,
                state=state,
                adapter_state=adapter_state,
                seconds=time.monotonic() - started,
            )

        if normalized.get("kind") == "goal_proof" or normalized.get("verdict") == "true":
            body = normalized.get("proof") or normalized.get("code")
            return ExecutionResult(
                status="candidate_ready" if isinstance(body, str) and body.strip() else "artifact_rejected",
                normalized_action=normalized,
                submitted_action=normalized,
                body=body if isinstance(body, str) and body.strip() else None,
                state={"kind": "DirectProofState", "status": "candidate_ready" if body else "missing_body"},
                adapter_state=adapter_state,
                seconds=time.monotonic() - started,
            )

        if baby_solver.is_hint_payload(normalized):
            tool = baby_solver.capability_tool_for_action(normalized)
            gate = baby_solver.capability_gate_state(tool, capability_mask)
            if gate is not None:
                return ExecutionResult(
                    status="capability_withheld",
                    normalized_action=normalized,
                    submitted_action=normalized,
                    state=gate,
                    adapter_state=adapter_state,
                    seconds=time.monotonic() - started,
                )
            body, state = baby_solver.hint_payload_attempt(
                normalized,
                h_eq,
                g_eq,
                capability_mask=capability_mask,
            )
        elif normalized.get("kind") == "tool_call":
            body, state = baby_solver.run_tool_call_detailed(
                normalized,
                h_eq,
                g_eq,
                capability_mask=capability_mask,
            )
        else:
            body, state = None, {
                "kind": "MechanicalExecutionState",
                "status": "unsupported_action",
            }
        return ExecutionResult(
            status="candidate_ready" if body else "mechanical_stuck",
            normalized_action=normalized,
            submitted_action=normalized,
            body=body,
            state=state or {},
            adapter_state=adapter_state,
            seconds=time.monotonic() - started,
        )
