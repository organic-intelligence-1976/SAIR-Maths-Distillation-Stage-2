"""Trusted episode state for capability-dropout lemma curricula.

The LLM may replace its whole answer on every turn.  This blackboard does not:
mechanically proved lemmas are retained, small-model-refuted lemmas are blocked
up to alpha-renaming and equality symmetry, and new proposals are composed with
the trusted partial plan before they return to the prover.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any

import baby_solver as solver


BLACKBOARD_PROTOCOL_VERSION = "lemma-blackboard-v1"


def _canonical_term(term: tuple, variables: dict[str, str]) -> str:
    if term[0] == "var":
        raw = str(term[1])
        if raw not in variables:
            variables[raw] = f"v{len(variables)}"
        return variables[raw]
    return f"({_canonical_term(term[1], variables)}◇{_canonical_term(term[2], variables)})"


def canonical_equation_signature(equation: str) -> str:
    """Canonicalize variable names and equation orientation.

    The signature is intentionally syntactic beyond alpha-renaming and equality
    symmetry.  It does not pretend to decide semantic equivalence.
    """
    parsed = solver.parse_equation(solver.clean_equation_hint_text(equation))

    def oriented(left: tuple, right: tuple) -> str:
        variables: dict[str, str] = {}
        return f"{_canonical_term(left, variables)}={_canonical_term(right, variables)}"

    return min(
        oriented(parsed["lhs"], parsed["rhs"]),
        oriented(parsed["rhs"], parsed["lhs"]),
    )


def _safe_name(value: Any, fallback: str, used: set[str]) -> str:
    base = re.sub(r"[^A-Za-z0-9_']", "_", str(value or "").strip())
    base = re.sub(r"_+", "_", base).strip("_") or fallback
    if not re.match(r"^[A-Za-z_]", base):
        base = fallback
    candidate = base
    suffix = 2
    while candidate in used:
        candidate = f"{base}_{suffix}"
        suffix += 1
    used.add(candidate)
    return candidate


def action_lemma_entries(action: dict[str, Any]) -> list[dict[str, Any]]:
    """Extract normalized lemma nodes while retaining seed/use arguments."""
    entries: list[dict[str, Any]] = []
    for hint in solver.parse_universal_equations(action):
        entry: dict[str, Any] = {
            "name": hint.name,
            "equation": hint.eq["text"],
            "signature": canonical_equation_signature(hint.eq["text"]),
        }
        if hint.seed_args:
            entry["seed_h_args"] = [list(row) for row in hint.seed_args]
        if hint.use_args:
            entry["use_args"] = [list(row) for row in hint.use_args]
        entries.append(entry)
    return entries


def _public_lemma(entry: dict[str, Any], name: str) -> dict[str, Any]:
    out: dict[str, Any] = {"name": name, "equation": entry["equation"]}
    for key in ("seed_h_args", "use_args"):
        if entry.get(key):
            out[key] = entry[key]
    return out


@dataclass
class LemmaBlackboard:
    """Monotone, mechanically attributed state for one proof episode."""

    trusted_nodes: dict[str, dict[str, Any]] = field(default_factory=dict)
    refuted_nodes: dict[str, dict[str, Any]] = field(default_factory=dict)
    events: list[dict[str, Any]] = field(default_factory=list)

    @classmethod
    def from_verified_snapshot(cls, snapshot: dict[str, Any] | None) -> "LemmaBlackboard":
        """Resume only mechanically attributed facts from a prior episode."""
        board = cls()
        source = snapshot if isinstance(snapshot, dict) else {}
        for row in source.get("trusted_nodes") or []:
            if not (
                isinstance(row, dict)
                and row.get("status") == "mechanically_proved"
                and isinstance(row.get("equation"), str)
            ):
                continue
            signature = canonical_equation_signature(row["equation"])
            board.trusted_nodes[signature] = {**row, "signature": signature}
        for row in source.get("refuted_nodes") or []:
            if not (
                isinstance(row, dict)
                and row.get("status") == "small_model_refuted"
                and isinstance(row.get("equation"), str)
            ):
                continue
            signature = canonical_equation_signature(row["equation"])
            if signature in board.trusted_nodes:
                continue
            board.refuted_nodes[signature] = {**row, "signature": signature}
        board.events.append({
            "kind": "LemmaBlackboardResume",
            "status": "verified_snapshot_loaded",
            "protocol_version": BLACKBOARD_PROTOCOL_VERSION,
            "trusted_node_count": len(board.trusted_nodes),
            "refuted_node_count": len(board.refuted_nodes),
        })
        return board

    def snapshot(self) -> dict[str, Any]:
        return {
            "protocol_version": BLACKBOARD_PROTOCOL_VERSION,
            "invariants": [
                "trusted nodes are immutable and automatically retained",
                "small-model-refuted nodes are blocked up to alpha-renaming and equality symmetry",
                "unproved nodes are not treated as false",
            ],
            "trusted_nodes": list(self.trusted_nodes.values()),
            "refuted_nodes": list(self.refuted_nodes.values()),
            "event_count": len(self.events),
        }

    def materialize_action(
        self,
        action: dict[str, Any],
        *,
        round_index: int,
    ) -> tuple[dict[str, Any] | None, dict[str, Any]]:
        """Compose an LLM hint with trusted nodes or reject a refuted repeat."""
        if not solver.is_hint_payload(action):
            return action, {
                "kind": "LemmaBlackboardState",
                "status": "non_lemma_action_passthrough",
                "protocol_version": BLACKBOARD_PROTOCOL_VERSION,
            }
        proposed = action_lemma_entries(action)
        if not proposed:
            return action, {
                "kind": "LemmaBlackboardState",
                "status": "no_parseable_plan_nodes",
                "protocol_version": BLACKBOARD_PROTOCOL_VERSION,
            }
        blocked = [
            {
                "proposed": entry,
                "prior_refutation": self.refuted_nodes[entry["signature"]],
            }
            for entry in proposed
            if entry["signature"] in self.refuted_nodes
        ]
        if blocked and len(blocked) == len(proposed):
            state = {
                "kind": "LemmaBlackboardState",
                "status": "blocked_refuted_repetition",
                "protocol_version": BLACKBOARD_PROTOCOL_VERSION,
                "blocked_nodes": blocked,
                "need_hint": (
                    "Replace every blocked node. A mechanically checked small model refutes "
                    "the same universal equation up to variable renaming/equality reversal."
                ),
            }
            self.events.append({"round": round_index, **state})
            return None, state

        proposed = [
            entry for entry in proposed
            if entry["signature"] not in self.refuted_nodes
        ]

        if not self.trusted_nodes:
            if blocked:
                used_names: set[str] = set()
                materialized = {
                    "kind": "tool_call",
                    "tool": "lemma_chain",
                    "target": "goal",
                    "lemmas": [
                        _public_lemma(
                            entry,
                            _safe_name(entry.get("name"), f"lemma_{index}", used_names),
                        )
                        for index, entry in enumerate(proposed, start=1)
                    ],
                }
                state = {
                    "kind": "LemmaBlackboardState",
                    "status": "refuted_nodes_filtered",
                    "protocol_version": BLACKBOARD_PROTOCOL_VERSION,
                    "blocked_nodes": blocked,
                    "new_node_count": len(proposed),
                    "materialized_action": materialized,
                }
                self.events.append({"round": round_index, **state})
                return materialized, state
            return action, {
                "kind": "LemmaBlackboardState",
                "status": "no_trusted_nodes_to_merge",
                "protocol_version": BLACKBOARD_PROTOCOL_VERSION,
                "new_node_count": len(proposed),
            }

        combined: list[dict[str, Any]] = []
        seen: set[str] = set()
        used_names: set[str] = set()
        retained = 0
        new_nodes = 0
        for entry in [*self.trusted_nodes.values(), *proposed]:
            signature = entry["signature"]
            if signature in seen:
                continue
            seen.add(signature)
            is_trusted = signature in self.trusted_nodes
            retained += int(is_trusted)
            new_nodes += int(not is_trusted)
            name = _safe_name(entry.get("name"), f"lemma_{len(combined) + 1}", used_names)
            combined.append(_public_lemma(entry, name))
        if new_nodes == 0:
            state = {
                "kind": "LemmaBlackboardState",
                "status": "no_new_plan_nodes",
                "protocol_version": BLACKBOARD_PROTOCOL_VERSION,
                "retained_node_count": retained,
                "need_hint": "All proposed lemmas are already trusted; add a new bridge node.",
            }
            self.events.append({"round": round_index, **state})
            return None, state
        materialized = {
            "kind": "tool_call",
            "tool": "lemma_chain",
            "target": "goal",
            "lemmas": combined,
        }
        state = {
            "kind": "LemmaBlackboardState",
            "status": "trusted_nodes_merged",
            "protocol_version": BLACKBOARD_PROTOCOL_VERSION,
            "retained_node_count": retained,
            "new_node_count": new_nodes,
            "materialized_action": materialized,
        }
        if blocked:
            state["blocked_nodes"] = blocked
            state["status"] = "trusted_nodes_merged_refuted_nodes_filtered"
        self.events.append({"round": round_index, **state})
        return materialized, state

    def absorb_mechanical_state(
        self,
        submitted_action: dict[str, Any] | None,
        mechanical_state: dict[str, Any] | None,
        *,
        round_index: int,
    ) -> dict[str, Any]:
        """Add only mechanically proved or decisively refuted nodes."""
        state = mechanical_state if isinstance(mechanical_state, dict) else {}
        submitted = {
            entry["signature"]: entry
            for entry in action_lemma_entries(submitted_action or {})
        }
        added_trusted: list[dict[str, Any]] = []
        added_refuted: list[dict[str, Any]] = []
        conflicts: list[dict[str, Any]] = []

        for proved in state.get("proved_lemmas") or []:
            equation = proved.get("equation") if isinstance(proved, dict) else None
            if not isinstance(equation, str):
                continue
            signature = canonical_equation_signature(equation)
            if signature in self.refuted_nodes:
                conflicts.append({"signature": signature, "kind": "proved_after_refuted"})
                continue
            if signature in self.trusted_nodes:
                continue
            source = submitted.get(signature) or {
                "name": proved.get("name") or f"trusted_{len(self.trusted_nodes) + 1}",
                "equation": equation,
                "signature": signature,
            }
            node = {
                **source,
                "status": "mechanically_proved",
                "verified_round": round_index,
            }
            self.trusted_nodes[signature] = node
            added_trusted.append(node)

        for failed in state.get("failed_midpoints") or []:
            if not isinstance(failed, dict):
                continue
            failure = failed.get("failure")
            equation = failed.get("equation")
            if not (
                isinstance(failure, dict)
                and failure.get("kind") == "small_model_refutation"
                and isinstance(equation, str)
            ):
                continue
            signature = canonical_equation_signature(equation)
            if signature in self.trusted_nodes:
                conflicts.append({"signature": signature, "kind": "refuted_after_proved"})
                continue
            if signature in self.refuted_nodes:
                continue
            node = {
                "name": failed.get("name"),
                "equation": equation,
                "signature": signature,
                "status": "small_model_refuted",
                "refuted_round": round_index,
                "refutation": failure,
            }
            self.refuted_nodes[signature] = node
            added_refuted.append(node)

        event = {
            "kind": "LemmaBlackboardUpdate",
            "status": "updated" if added_trusted or added_refuted else "no_decisive_node_update",
            "protocol_version": BLACKBOARD_PROTOCOL_VERSION,
            "round": round_index,
            "added_trusted": added_trusted,
            "added_refuted": added_refuted,
            "conflicts": conflicts,
            "trusted_node_count": len(self.trusted_nodes),
            "refuted_node_count": len(self.refuted_nodes),
        }
        self.events.append(event)
        return event
