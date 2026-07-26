"""Trusted mechanical execution adapter over the current packed solver engines."""

from __future__ import annotations

import time
from typing import Any

import baby_solver

from .protocol import ExecutionResult, ProblemSpec, SemanticRecord


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
        return baby_solver.normalize_llm_action(action)

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
