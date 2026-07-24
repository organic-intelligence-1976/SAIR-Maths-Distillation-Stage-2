"""Minimal verified episode-to-strategy distillation."""

from __future__ import annotations

import hashlib
import json
from typing import Any

from .protocol import EpisodeRecord, ExecutionResult, StrategyArtifact
from .structure import canonical_equation_signature, problem_structure


PROOF_PLAN_LESSON_VERSION = "sair-proof-plan-lesson-v1"


def _failure_signals(episode: EpisodeRecord) -> list[dict[str, Any]]:
    signals: list[dict[str, Any]] = []
    seen: set[str] = set()
    for attempt in episode.attempts:
        if not isinstance(attempt, dict) or attempt.get("status") == "accepted":
            continue
        execution = attempt.get("execution") if isinstance(attempt.get("execution"), dict) else {}
        state = execution.get("state") if isinstance(execution.get("state"), dict) else {}
        need_hint = state.get("need_hint")
        hint_kind = need_hint.get("kind") if isinstance(need_hint, dict) else None
        signal = {
            "attempt_status": attempt.get("status"),
            "state_kind": state.get("kind"),
            "state_status": state.get("status"),
            "need_hint_kind": hint_kind,
        }
        key = json.dumps(signal, sort_keys=True)
        if key in seen or all(value is None for value in signal.values()):
            continue
        seen.add(key)
        signals.append(signal)
        if len(signals) >= 6:
            break
    return signals


class VerifiedDistiller:
    name = "verified_distiller_v1"

    @staticmethod
    def _id(payload: dict[str, Any]) -> str:
        digest = hashlib.sha256(json.dumps(payload, sort_keys=True).encode("utf-8")).hexdigest()[:16]
        return f"strategy_{digest}"

    def distill(
        self,
        episode: EpisodeRecord,
        execution: ExecutionResult | None,
    ) -> StrategyArtifact | None:
        if not episode.accepted or execution is None:
            return None
        semantics = episode.semantics
        trigger = {
            "semantic_class": semantics.get("semantic_class"),
            "general_status": semantics.get("general_status"),
            "finite_status": semantics.get("finite_status"),
            "problem_structure": problem_structure(episode.problem),
            "capability_context": episode.capability_mask,
        }
        trusted = episode.blackboard.get("trusted_nodes") or []
        if execution.body and trusted:
            kind = "proof_plan_schema"
            obligation_by_signature = {
                str(node.get("signature")): node
                for node in episode.obligations.get("nodes") or []
                if isinstance(node, dict) and node.get("signature")
            }
            plan_nodes = []
            predecessors: list[str] = []
            for row in trusted:
                equation = row.get("equation") if isinstance(row, dict) else None
                if not isinstance(equation, str):
                    continue
                signature = canonical_equation_signature(equation)
                obligation = obligation_by_signature.get(signature, {})
                plan_nodes.append({
                    "node_id": f"lemma_{len(plan_nodes) + 1}",
                    "name": row.get("name"),
                    "equation": equation,
                    "signature": signature,
                    "status": "mechanically_proved",
                    "verified_round": row.get("verified_round"),
                    "predecessors_available": list(predecessors),
                    "depends_on": list(obligation.get("depends_on") or []),
                    "family_id": obligation.get("family_id"),
                    "mechanism": obligation.get("mechanism"),
                    "mechanism_signature": obligation.get("mechanism_signature"),
                    "alternative_group": obligation.get("alternative_group"),
                    "advances": obligation.get("advances"),
                })
                predecessors.append(signature)
            action_template = {
                "kind": "tool_call",
                "tool": "lemma_chain",
                "target": "goal",
                "lemmas": [
                    {"name": row.get("name"), "equation": row.get("equation")}
                    for row in plan_nodes
                ],
            }
            payload = {
                "kind": "verified_proof_plan_lesson",
                "lesson_schema": PROOF_PLAN_LESSON_VERSION,
                "plan_nodes": plan_nodes,
                "action_template": action_template,
                "observed_failure_signals": _failure_signals(episode),
                "outcome": {
                    "verdict": (episode.verification or {}).get("verdict"),
                    "accepted": True,
                },
            }
            deployability = "competition_candidate"
        elif execution.finite_table is not None:
            kind = "model_instance"
            payload = {
                "carrier_size": len(execution.finite_table),
                "table": execution.finite_table,
            }
            deployability = "competition_candidate"
        elif execution.infinite_code:
            kind = "infinite_model_artifact"
            payload = {
                "artifact_sha256": hashlib.sha256(execution.infinite_code.encode("utf-8")).hexdigest(),
                "artifact_bytes": len(execution.infinite_code.encode("utf-8")),
            }
            deployability = "research_only"
        else:
            return None
        identity = {"kind": kind, "trigger": trigger, "payload": payload}
        return StrategyArtifact(
            artifact_id=self._id(identity),
            kind=kind,
            status="verified",
            deployability=deployability,
            trigger=trigger,
            payload=payload,
            evidence={
                "episode_id": episode.episode_id,
                "case_id": episode.case_id,
                "verification": episode.verification,
            },
        )
