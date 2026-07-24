"""Approach-family-aware AND/OR obligation registry for proof-plan search."""

from __future__ import annotations

import re
import zlib
from dataclasses import asdict, dataclass, field
from typing import Any

import baby_solver

from .structure import canonical_equation_signature


OBLIGATION_PROTOCOL_VERSION = "sair-obligation-graph-v1"
PLAN_ACTION_KINDS = {"proof_plan", "lemma_dag", "obligation_plan"}
PLAN_ACTION_TOOLS = {"proof_plan", "lemma_dag", "obligation_graph"}


def _safe_id(value: Any, fallback: str) -> str:
    text = re.sub(r"[^a-zA-Z0-9_'-]+", "_", str(value or "").strip()).strip("_")
    return text or fallback


def _normalized_text(value: Any) -> str:
    return re.sub(r"\s+", " ", str(value or "").strip().lower())


def _mechanism_signature(*parts: Any) -> str:
    normalized = "|".join(_normalized_text(part) for part in parts if str(part or "").strip())
    return f"mechanism_{zlib.crc32(normalized.encode('utf-8')) & 0xFFFFFFFF:08x}"


def _projection_family(parsed: dict[str, Any]) -> str | None:
    for left, right in ((parsed["lhs"], parsed["rhs"]), (parsed["rhs"], parsed["lhs"])):
        if left[0] == "op" and right[0] == "var":
            if left[1] == right:
                return "left_projection"
            if left[2] == right:
                return "right_projection"
    return None


def _row_family(parsed: dict[str, Any]) -> str | None:
    left, right = parsed["lhs"], parsed["rhs"]
    if left[0] != "op" or right[0] != "op":
        return None
    if left[1] == right[1] and left[2] != right[2]:
        return "row_constancy"
    if left[2] == right[2] and left[1] != right[1]:
        return "column_constancy"
    variables = [term for term in (left[1], left[2], right[1], right[2]) if term[0] == "var"]
    if len(variables) == 4 and len({term[1] for term in variables}) >= 3:
        return "operation_collapse"
    return None


def infer_approach_family(equation: str, declared: Any = None) -> str:
    """Prefer mechanically recognizable mechanism families over free-form labels."""
    try:
        parsed = baby_solver.parse_equation(equation)
        helper = baby_solver.helper_kind(equation)
        if helper in {"square_absorb", "right_square", "square_const", "right_id_square"}:
            return "square_normalization"
        if helper in {"sandwich", "left_sandwich"}:
            return "sandwich_normalization"
        projection = _projection_family(parsed)
        if projection:
            return projection
        row = _row_family(parsed)
        if row:
            return row
    except Exception:
        pass
    return _safe_id(declared, "unclassified_lemma")


def is_obligation_plan_action(action: Any) -> bool:
    if not isinstance(action, dict):
        return False
    kind = str(action.get("kind") or "").strip()
    tool = str(action.get("tool") or "").strip()
    return kind in PLAN_ACTION_KINDS or (kind == "tool_call" and tool in PLAN_ACTION_TOOLS)


@dataclass
class ObligationNode:
    node_id: str
    equation: str
    signature: str
    family_id: str
    declared_family_id: str
    mechanism_signature: str
    mechanism: str
    depends_on: list[str] = field(default_factory=list)
    alternative_group: str | None = None
    advances: str = "root"
    status: str = "proposed"
    attempts: int = 0
    reopen_count: int = 0
    blocked_reason: str | None = None
    mechanism_history: list[str] = field(default_factory=list)
    evidence: list[dict[str, Any]] = field(default_factory=list)

    def to_mapping(self) -> dict[str, Any]:
        return asdict(self)


class ObligationGraph:
    """Persistent lemma obligations with explicit OR families and AND dependencies."""

    def __init__(self, *, block_after_attempts: int = 2):
        self.block_after_attempts = max(1, int(block_after_attempts))
        self.nodes: dict[str, ObligationNode] = {}
        self.signature_index: dict[str, str] = {}
        self.events: list[dict[str, Any]] = []

    @classmethod
    def from_snapshot(cls, snapshot: dict[str, Any] | None) -> "ObligationGraph":
        source = snapshot if isinstance(snapshot, dict) else {}
        graph = cls(block_after_attempts=int(source.get("block_after_attempts") or 2))
        for row in source.get("nodes") or []:
            if not isinstance(row, dict):
                continue
            try:
                equation = str(row["equation"])
                signature = canonical_equation_signature(equation)
            except Exception:
                continue
            node_id = _safe_id(row.get("node_id"), f"node_{len(graph.nodes) + 1}")
            if node_id in graph.nodes or signature in graph.signature_index:
                continue
            node = ObligationNode(
                node_id=node_id,
                equation=equation,
                signature=signature,
                family_id=_safe_id(row.get("family_id"), "unclassified_lemma"),
                declared_family_id=_safe_id(row.get("declared_family_id"), "unclassified_lemma"),
                mechanism_signature=str(row.get("mechanism_signature") or _mechanism_signature(equation)),
                mechanism=str(row.get("mechanism") or ""),
                depends_on=[str(item) for item in row.get("depends_on") or []],
                alternative_group=str(row["alternative_group"]) if row.get("alternative_group") else None,
                advances=str(row.get("advances") or "root"),
                status=str(row.get("status") or "proposed"),
                attempts=max(0, int(row.get("attempts") or 0)),
                reopen_count=max(0, int(row.get("reopen_count") or 0)),
                blocked_reason=str(row["blocked_reason"]) if row.get("blocked_reason") else None,
                mechanism_history=[str(item) for item in row.get("mechanism_history") or []],
                evidence=[item for item in row.get("evidence") or [] if isinstance(item, dict)][-12:],
            )
            graph.nodes[node_id] = node
            graph.signature_index[signature] = node_id
        graph.events = [item for item in source.get("events") or [] if isinstance(item, dict)][-100:]
        graph.events.append({
            "kind": "ObligationGraphResume",
            "status": "verified_state_loaded",
            "node_count": len(graph.nodes),
        })
        graph._propagate_dependency_blocks()
        return graph

    def _unique_node_id(self, requested: Any) -> str:
        base = _safe_id(requested, f"node_{len(self.nodes) + 1}")
        node_id = base
        suffix = 2
        while node_id in self.nodes:
            node_id = f"{base}_{suffix}"
            suffix += 1
        return node_id

    def _register_entry(self, entry: dict[str, Any], *, round_index: int) -> dict[str, Any]:
        equation = entry.get("equation") or entry.get("lemma") or entry.get("claim")
        if not isinstance(equation, str) or "=" not in equation:
            return {"status": "rejected", "reason": "missing_parseable_equation"}
        try:
            cleaned = baby_solver.clean_equation_hint_text(equation)
            signature = canonical_equation_signature(cleaned)
        except Exception as exc:
            return {"status": "rejected", "reason": "equation_parse_error", "error": repr(exc)}
        existing_id = self.signature_index.get(signature)
        declared_family = _safe_id(entry.get("family_id") or entry.get("family"), "unclassified_lemma")
        family = infer_approach_family(cleaned, declared_family)
        mechanism = str(entry.get("mechanism") or entry.get("why") or family)
        novelty = str(entry.get("reopen_novelty") or "").strip()
        mechanism_signature = _mechanism_signature(family, mechanism, novelty)
        if existing_id is not None:
            node = self.nodes[existing_id]
            if node.status == "proved":
                return {"status": "already_proved", "node_id": node.node_id, "signature": signature}
            if node.status == "refuted":
                return {"status": "rejected_refuted_repetition", "node_id": node.node_id, "signature": signature}
            if node.status == "blocked":
                if len(novelty) < 8:
                    return {
                        "status": "rejected_blocked_without_novelty",
                        "node_id": node.node_id,
                        "blocked_reason": node.blocked_reason,
                    }
                if mechanism_signature in node.mechanism_history:
                    return {
                        "status": "rejected_duplicate_reopen_mechanism",
                        "node_id": node.node_id,
                    }
                node.status = "proposed"
                node.blocked_reason = None
                node.reopen_count += 1
                node.mechanism = mechanism
                node.mechanism_signature = mechanism_signature
                node.mechanism_history.append(mechanism_signature)
                node.evidence.append({
                    "round": round_index,
                    "kind": "reopened",
                    "reopen_novelty": novelty,
                })
                return {"status": "reopened_with_novelty", "node_id": node.node_id}
            return {"status": "existing_active_node", "node_id": node.node_id}

        node_id = self._unique_node_id(entry.get("id") or entry.get("node_id") or entry.get("name"))
        depends_on = [str(item) for item in entry.get("depends_on") or entry.get("dependencies") or []]
        node = ObligationNode(
            node_id=node_id,
            equation=cleaned,
            signature=signature,
            family_id=family,
            declared_family_id=declared_family,
            mechanism_signature=mechanism_signature,
            mechanism=mechanism,
            depends_on=depends_on,
            alternative_group=str(entry.get("alternative_group") or entry.get("or_group"))
            if entry.get("alternative_group") or entry.get("or_group")
            else None,
            advances=str(entry.get("advances") or entry.get("target_obligation") or "root"),
            mechanism_history=[mechanism_signature],
            evidence=[{"round": round_index, "kind": "proposed"}],
        )
        self.nodes[node_id] = node
        self.signature_index[signature] = node_id
        return {
            "status": "registered",
            "node_id": node_id,
            "family_id": family,
            "declared_family_id": declared_family,
            "signature": signature,
        }

    def synchronize_blackboard(self, blackboard: dict[str, Any] | None, *, round_index: int) -> None:
        trusted = {
            canonical_equation_signature(str(row["equation"]))
            for row in (blackboard or {}).get("trusted_nodes") or []
            if isinstance(row, dict) and isinstance(row.get("equation"), str)
        }
        refuted = {
            canonical_equation_signature(str(row["equation"]))
            for row in (blackboard or {}).get("refuted_nodes") or []
            if isinstance(row, dict) and isinstance(row.get("equation"), str)
        }
        for signature in trusted:
            node_id = self.signature_index.get(signature)
            if node_id and self.nodes[node_id].status != "proved":
                node = self.nodes[node_id]
                node.status = "proved"
                node.blocked_reason = None
                node.evidence.append({"round": round_index, "kind": "blackboard_proved"})
        for signature in refuted:
            node_id = self.signature_index.get(signature)
            if node_id and self.nodes[node_id].status != "refuted":
                node = self.nodes[node_id]
                node.status = "refuted"
                node.blocked_reason = "mechanically_refuted"
                node.evidence.append({"round": round_index, "kind": "blackboard_refuted"})
        self._propagate_dependency_blocks()

    def _propagate_dependency_blocks(self) -> None:
        for node in self.nodes.values():
            if node.status in {"proved", "refuted"}:
                continue
            failed = [
                dependency
                for dependency in node.depends_on
                if dependency in self.nodes and self.nodes[dependency].status in {"refuted", "blocked"}
            ]
            if failed:
                node.status = "blocked"
                node.blocked_reason = f"blocked_dependencies:{','.join(failed)}"

    def _ready_nodes(self) -> list[ObligationNode]:
        ready = []
        for node in self.nodes.values():
            if node.status not in {"proposed", "retryable"}:
                continue
            if all(
                dependency in self.nodes and self.nodes[dependency].status == "proved"
                for dependency in node.depends_on
            ):
                ready.append(node)
        return ready

    def materialize(
        self,
        *,
        round_index: int,
        limit: int = 5,
        unattempted_only: bool = False,
    ) -> tuple[dict[str, Any] | None, dict[str, Any]]:
        """Select a diversity-first batch without assigning fixed family quotas."""
        ready = self._ready_nodes()
        if unattempted_only:
            ready = [node for node in ready if node.attempts == 0]
        family_attempts: dict[str, int] = {}
        for node in self.nodes.values():
            family_attempts[node.family_id] = family_attempts.get(node.family_id, 0) + node.attempts
        ready.sort(key=lambda node: (family_attempts.get(node.family_id, 0), node.attempts, node.node_id))
        selected: list[ObligationNode] = []
        selected_families: set[str] = set()
        for node in ready:
            if node.family_id in selected_families:
                continue
            selected.append(node)
            selected_families.add(node.family_id)
            if len(selected) >= max(1, limit):
                break
        if len(selected) < max(1, limit):
            for node in ready:
                if node in selected:
                    continue
                selected.append(node)
                if len(selected) >= max(1, limit):
                    break
        if not selected:
            state = {
                "kind": "ObligationGraphState",
                "status": "no_runnable_obligations",
                "protocol_version": OBLIGATION_PROTOCOL_VERSION,
                "blocked_nodes": [node.node_id for node in self.nodes.values() if node.status == "blocked"],
                "unmet_dependencies": {
                    node.node_id: [dep for dep in node.depends_on if dep not in self.nodes or self.nodes[dep].status != "proved"]
                    for node in self.nodes.values()
                    if node.status in {"proposed", "retryable"} and node.depends_on
                },
                "unattempted_only": unattempted_only,
            }
            return None, state
        for node in selected:
            node.status = "active"
            node.attempts += 1
            node.evidence.append({"round": round_index, "kind": "materialized", "attempt": node.attempts})
        action = {
            "kind": "tool_call",
            "tool": "lemma_chain",
            "target": "goal",
            "lemmas": [
                {"name": node.node_id, "equation": node.equation}
                for node in selected
            ],
        }
        state = {
            "kind": "ObligationGraphState",
            "status": "runnable_batch_materialized",
            "protocol_version": OBLIGATION_PROTOCOL_VERSION,
            "selected_nodes": [node.node_id for node in selected],
            "selected_families": [node.family_id for node in selected],
            "ready_node_count": len(ready),
            "diversity_first": True,
            "unattempted_only": unattempted_only,
        }
        return action, state

    def materialize_unattempted(
        self,
        *,
        blackboard: dict[str, Any] | None,
        round_index: int,
        limit: int = 5,
    ) -> tuple[dict[str, Any] | None, dict[str, Any]]:
        self.synchronize_blackboard(blackboard, round_index=round_index)
        return self.materialize(
            round_index=round_index,
            limit=limit,
            unattempted_only=True,
        )

    def prepare_action(
        self,
        action: dict[str, Any],
        *,
        blackboard: dict[str, Any] | None,
        round_index: int,
        limit: int = 5,
    ) -> tuple[dict[str, Any] | None, dict[str, Any]]:
        self.synchronize_blackboard(blackboard, round_index=round_index)
        if is_obligation_plan_action(action):
            rows = action.get("nodes") or action.get("obligations") or action.get("candidates") or []
            if not isinstance(rows, list):
                rows = []
            ingest = [
                self._register_entry(row, round_index=round_index)
                for row in rows
                if isinstance(row, dict)
            ]
            materialized, state = self.materialize(
                round_index=round_index,
                limit=int(action.get("max_parallel") or limit),
            )
            state["ingest"] = ingest
            state["raw_plan_kind"] = action.get("kind")
            self.events.append({"round": round_index, **state})
            return materialized, state

        if baby_solver.is_hint_payload(action):
            observed = []
            for index, hint in enumerate(baby_solver.parse_universal_equations(action), start=1):
                observed.append(self._register_entry({
                    "id": hint.name or f"legacy_{index}",
                    "equation": hint.eq["text"],
                    "family_id": action.get("family_id") or "legacy_unclassified",
                    "mechanism": action.get("why") or "legacy lemma action",
                }, round_index=round_index))
            state = {
                "kind": "ObligationGraphState",
                "status": "legacy_lemma_action_registered",
                "protocol_version": OBLIGATION_PROTOCOL_VERSION,
                "ingest": observed,
            }
            self.events.append({"round": round_index, **state})
            return action, state

        state = {
            "kind": "ObligationGraphState",
            "status": "non_lemma_action_passthrough",
            "protocol_version": OBLIGATION_PROTOCOL_VERSION,
        }
        return action, state

    def absorb_mechanical_state(
        self,
        submitted_action: dict[str, Any] | None,
        mechanical_state: dict[str, Any] | None,
        *,
        round_index: int,
        accepted: bool = False,
    ) -> dict[str, Any]:
        state = mechanical_state if isinstance(mechanical_state, dict) else {}
        proved = {
            canonical_equation_signature(str(row["equation"]))
            for row in state.get("proved_lemmas") or []
            if isinstance(row, dict) and isinstance(row.get("equation"), str)
        }
        refuted = set()
        for row in state.get("failed_midpoints") or []:
            if not isinstance(row, dict) or not isinstance(row.get("equation"), str):
                continue
            failure = row.get("failure")
            if isinstance(failure, dict) and failure.get("kind") == "small_model_refutation":
                refuted.add(canonical_equation_signature(str(row["equation"])))
        submitted_signatures = {
            canonical_equation_signature(hint.eq["text"])
            for hint in baby_solver.parse_universal_equations(submitted_action or {})
        }
        transitions = []
        for signature in submitted_signatures:
            node_id = self.signature_index.get(signature)
            if not node_id:
                continue
            node = self.nodes[node_id]
            prior = node.status
            if signature in proved:
                node.status = "proved"
                node.blocked_reason = None
                evidence_kind = "mechanically_proved"
            elif signature in refuted:
                node.status = "refuted"
                node.blocked_reason = "small_model_refutation"
                evidence_kind = "mechanically_refuted"
            elif node.attempts >= self.block_after_attempts:
                node.status = "blocked"
                node.blocked_reason = "repeated_budgeted_attempts_without_decisive_progress"
                evidence_kind = "blocked_after_attempt_limit"
            else:
                node.status = "retryable"
                evidence_kind = "budgeted_attempt_inconclusive"
            node.evidence.append({
                "round": round_index,
                "kind": evidence_kind,
                "mechanical_status": state.get("status"),
            })
            transitions.append({"node_id": node_id, "from": prior, "to": node.status})
        self._propagate_dependency_blocks()
        event = {
            "kind": "ObligationGraphUpdate",
            "status": "root_accepted" if accepted else "updated",
            "protocol_version": OBLIGATION_PROTOCOL_VERSION,
            "round": round_index,
            "transitions": transitions,
        }
        self.events.append(event)
        return event

    def snapshot(self) -> dict[str, Any]:
        family_rows = []
        for family_id in sorted({node.family_id for node in self.nodes.values()}):
            members = [node for node in self.nodes.values() if node.family_id == family_id]
            statuses: dict[str, int] = {}
            for node in members:
                statuses[node.status] = statuses.get(node.status, 0) + 1
            family_rows.append({
                "family_id": family_id,
                "node_count": len(members),
                "attempt_count": sum(node.attempts for node in members),
                "statuses": statuses,
                "crowding": len(members),
            })
        return {
            "protocol_version": OBLIGATION_PROTOCOL_VERSION,
            "block_after_attempts": self.block_after_attempts,
            "invariants": [
                "proved and refuted states require mechanical evidence",
                "dependencies are AND obligations; ready alternatives are diversity scheduled",
                "blocked exact nodes require an explicit new mechanism to reopen",
                "family labels prefer mechanically inferred equation shapes over free-form names",
            ],
            "nodes": [node.to_mapping() for node in self.nodes.values()],
            "families": family_rows,
            "ready_nodes": [node.node_id for node in self._ready_nodes()],
            "blocked_nodes": [node.node_id for node in self.nodes.values() if node.status == "blocked"],
            "events": self.events[-100:],
        }

    def planner_view(self, *, max_nodes: int = 16) -> dict[str, Any]:
        snapshot = self.snapshot()
        priority = {"proposed": 0, "retryable": 1, "blocked": 2, "active": 3, "proved": 4, "refuted": 5}
        nodes = sorted(
            self.nodes.values(),
            key=lambda node: (priority.get(node.status, 9), node.attempts, node.node_id),
        )[:max(1, int(max_nodes))]
        return {
            "protocol_version": OBLIGATION_PROTOCOL_VERSION,
            "invariants": snapshot["invariants"],
            "families": snapshot["families"],
            "ready_nodes": snapshot["ready_nodes"],
            "blocked_nodes": snapshot["blocked_nodes"],
            "nodes": [
                {
                    "node_id": node.node_id,
                    "equation": node.equation,
                    "family_id": node.family_id,
                    "mechanism": node.mechanism,
                    "depends_on": node.depends_on,
                    "alternative_group": node.alternative_group,
                    "advances": node.advances,
                    "status": node.status,
                    "attempts": node.attempts,
                    "blocked_reason": node.blocked_reason,
                }
                for node in nodes
            ],
            "recent_events": self.events[-6:],
        }


__all__ = [
    "OBLIGATION_PROTOCOL_VERSION",
    "ObligationGraph",
    "ObligationNode",
    "infer_approach_family",
    "is_obligation_plan_action",
]
