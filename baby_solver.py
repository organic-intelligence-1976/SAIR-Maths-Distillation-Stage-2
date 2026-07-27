#!/usr/bin/env python3
"""Baby collaborative solver for SAIR Stage 2.

This is intentionally not the big coverage-oriented mechanical solver. It is a
compact, submittable sketch of the newer LLM/mechanical architecture:

1. trusted mechanical tools produce Lean or countermodels;
2. the LLM may only choose tools or propose helper equations/tables;
3. every candidate is checked by the official judge before we stop.

The file is self-contained and uses only the Solo stdin/stdout protocol.
"""

from __future__ import annotations

import ast
from copy import deepcopy
import json
import random
import re
import select
import signal
import sys
import textwrap
import time
import difflib
import zlib
from collections import Counter
from dataclasses import dataclass, field
from itertools import product
from typing import Any


PROMPT = """You are steering trusted mechanical tools for a magma equation problem.
The magma operator is ◇, never *.

Problem {problem.id}:
  H    : {problem.equation1}
  Goal : {problem.equation2}

Problem analysis:
{solver.problem_analysis}

Mechanical analysis:
{solver.analysis}

Tool registry:
{solver.tool_registry}

Recommended tool calls:
{solver.tool_advice}

Strategy cards:
{solver.strategy_cards}

Phase directive:
{solver.phase_directive}

Previous attempts:
{history.attempts}

Mechanical feedback from solver-side hint attempts:
{solver.mechanical_feedback}

Few-shot tool-call guidance:
{solver.fewshots}

Current collaboration goal:
{solver.collaboration_goal}

Return exactly one JSON object, no prose, no markdown, no chain-of-thought.
Keep ordinary actions under 600 characters. When the phase explicitly enables
a symbolic type-level model, a complete Lean artifact or structured model plan
may use the official 20,000-byte false-certificate envelope. Prefer structured
parts over rewriting a whole artifact after a local Lean error.

Allowed responses:
There is no tool named "true_midpoint"; true-side bridges must use
{"kind":"midpoint","lemma":"<equation>"} or {"kind":"tool_call","tool":"lemma_chain","lemmas":[...]}.
{"kind":"tool_call","tool":"right_square_chain","target":"goal","why":"H has x = (y ◇ (y ◇ z)) ◇ (x ◇ x)"}
{"kind":"tool_call","tool":"square_sandwich_chain","target":"goal","why":"H has x = ((y ◇ x) ◇ y) ◇ (z ◇ z)"}
{"kind":"tool_call","tool":"rowconst_certificates","target":"goal","why":"try row-constant certificates"}
{"kind":"tool_call","tool":"grounding_derived","target":"goal","why":"try the square-rowconst grounding-derived closer"}
{"kind":"tool_call","tool":"broad_grounding_derived","target":"goal","budget":12,"why":"derive collapse or factor-irrelevance helper"}
{"kind":"tool_call","tool":"collapse_certificates","target":"goal","why":"try carrier-collapse certificates"}
{"kind":"tool_call","tool":"proof_battery","target":"goal","why":"try graph-first old battery h-instances"}
{"kind":"tool_call","tool":"forward_saturation","target":"goal","seed_terms":["x ◇ y","(x ◇ y) ◇ x"],"budget":3,"why":"try graph proof with extra seed terms"}
{"kind":"tool_call","tool":"goal_superposition","target":"goal","budget":8,"why":"try broad proof-carrying superposition when graph search is stuck"}
{"kind":"tool_call","tool":"standard_aux_superposition","target":"goal","lemmas":["const","proj_l","proj_r","rowconst"],"budget":10,"why":"try standard collapse/projection/rowconst lemmas"}
{"kind":"midpoint","lemma":"a ◇ b = c ◇ d","why":"direct opconst bridge when feedback shows an opconst-like derived equation"}
{"kind":"tool_call","tool":"lemma_chain","target":"goal","lemmas":[{"name":"square_absorb","equation":"u ◇ (v ◇ v) = v"},{"name":"right_square","equation":"u ◇ v = v ◇ v"}]}
{"kind":"tool_call","tool":"lemma_chain","target":"goal","lemmas":[{"name":"square_const","equation":"u ◇ u = v ◇ v"},{"name":"right_id_square","equation":"u ◇ (v ◇ v) = u"},{"name":"sandwich","equation":"(v ◇ u) ◇ v = u"},{"name":"left_sandwich","equation":"v ◇ (u ◇ v) = u"}]}
{"kind":"midpoint","lemma":"a ◇ (b ◇ b) = b","why":"one bridge equation; solver proves H=>lemma and H+lemma=>Goal"}
{"kind":"midpoint_chain","lemmas":["a ◇ a = b ◇ b","a ◇ (b ◇ b) = a"],"why":"short chain; each proved before use"}
{"kind":"tool_call","tool":"false_model_search","target":"goal","template":"local_search","routes":["local_search:n=6:seed=2"],"budget":6}
{"kind":"tool_call","tool":"false_model_search","target":"goal","template":"model_finder","routes":["model_finder:n=4"],"budget":6}
{"kind":"tool_call","tool":"false_model_search","target":"goal","template":"model_finder_v2","routes":["model_finder_v2:n=6"],"budget":8}
{"kind":"tool_call","tool":"false_model_search","target":"goal","template":"poly_ce","routes":["poly_ce:tier=2:nmax=13"],"budget":8}
{"kind":"tool_call","tool":"false_model_search","target":"goal","template":"structured_ce","routes":["structured_ce:max_n=7"],"budget":8}
{"kind":"tool_call","tool":"false_model_search","target":"goal","template":"cp_sat","routes":["cp_sat:n=5"],"budget":10}
{"kind":"tool_call","tool":"false_model_search","target":"goal","template":"skew_product","routes":["skew_product:2x3"],"budget":4}
{"kind":"tool_call","tool":"false_model_search","target":"goal","template":"sympy_sat","routes":["sympy_sat:n=6"],"budget":120}
{"kind":"false_model_family","carrier_size":8,"default":{"kind":"affine","params":[1,0,0]},"rules":[{"when":{"kind":"diagonal"},"value":"i+1"}],"budget":8}
{"kind":"symbolic_model_plan","representation":"infinite","model_name":"model","imports":["Mathlib.Tactic"],"carrier":"ℕ","definitions":["let parity : Nat → Bool := ...","let op (x y : Nat) := ..."],"operation":"op","setup":["have helper : ... := by\n  ..."],"hypothesis_proof":"intro x y z\n...","counterexample_proof":"intro goal_holds\nhave h := goal_holds ...\n..."}
{"kind":"symbolic_model_patch","set":{"hypothesis_proof":"intro x y z\n<complete repaired tactic body>"}}
{"kind":"goal_proof","proof":"intro x y\\nhave h1 := h x x x\\ngrind"}
{"kind":"false_table","counterexample_table":[[0,1],[1,0]]}

The equations in midpoint, midpoint_chain, and lemma_chain are untrusted hints.
The solver tries to prove each helper from H before using it. Bad hints are
ignored. If mechanical_feedback reports that a tool call or midpoint failed, do
not repeat the exact same call; repair it or switch strategy.
If phase_directive or allowed_action_override narrows the response kinds,
that narrower contract overrides the generic examples above.
Do not write Lean unless you return kind=goal_proof, kind=infinite_model,
kind=symbolic_model_plan, or kind=symbolic_model_patch.
Prefer tool_call, midpoint, midpoint_chain, lemma_hint, lemma_chain,
false_model_family, symbolic_model_plan, symbolic_model_patch, or false_table.
"""


# Protocol


def read_msg() -> dict[str, Any]:
    line = sys.stdin.readline()
    if not line:
        sys.exit(0)
    return json.loads(line)


def send_msg(msg: dict[str, Any]) -> None:
    print(json.dumps(msg), flush=True)


def call_judge(verdict: str, code: str) -> dict[str, Any]:
    send_msg({"call": "judge", "verdict": verdict, "code": code})
    return read_msg()


def call_llm(context: dict[str, Any]) -> dict[str, Any]:
    send_msg({"call": "llm", "context": context})
    return read_msg()


PROTOCOL_VERSION = "sair-collab-protocol-v0"


@dataclass(frozen=True)
class ProtocolIssue:
    """Small normalized diagnostic for the LLM/mechanical adapter boundary."""

    code: str
    message: str
    field: str | None = None

    def to_dict(self) -> dict[str, Any]:
        out = {"code": self.code, "message": self.message}
        if self.field:
            out["field"] = self.field
        return out


def protocol_state(
    kind: str,
    status: str,
    source: str,
    **extra: Any,
) -> dict[str, Any]:
    """Build a protocol-v0 feedback object while preserving plain dict ergonomics."""
    out: dict[str, Any] = {
        "protocol_version": PROTOCOL_VERSION,
        "kind": kind,
        "status": status,
        "source": source,
    }
    contract = tool_contract(extra.get("tool") or source) if "tool_contract" not in extra else None
    if contract:
        out["tool_contract"] = contract
    for key, value in extra.items():
        if value is not None:
            out[key] = value
    return out


def protocolize_state(
    state: dict[str, Any] | None,
    source: str,
    *,
    status: str | None = None,
    suggested_next_actions: list[dict[str, Any]] | None = None,
    errors: list[dict[str, Any]] | None = None,
    **extra: Any,
) -> dict[str, Any]:
    """Add protocol-v0 metadata to existing module states without wrapping them."""
    out = dict(state or {})
    out.setdefault("protocol_version", PROTOCOL_VERSION)
    out.setdefault("kind", "MechanicalState")
    if "source" in out and out["source"] != source:
        out.setdefault("artifact_source", out["source"])
    out["source"] = source
    contract = tool_contract(out.get("tool") or source)
    if contract:
        out.setdefault("tool_contract", contract)
    if status is not None:
        out["status"] = status
    else:
        out.setdefault("status", "unknown")
    if suggested_next_actions:
        out["suggested_next_actions"] = suggested_next_actions
    if errors:
        out["errors"] = errors
    for key, value in extra.items():
        if value is not None:
            out[key] = value
    return out


# Renewable budget allocation


def _finite_float(value: Any, default: float) -> float:
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return default
    if parsed != parsed or parsed in (float("inf"), float("-inf")):
        return default
    return parsed


def _clamped_float(value: Any, default: float, low: float, high: float) -> float:
    return max(low, min(high, _finite_float(value, default)))


def _clamped_int(value: Any, default: int, low: int, high: int) -> int:
    try:
        parsed = int(value)
    except (TypeError, ValueError):
        return default
    return max(low, min(high, parsed))


@dataclass(frozen=True)
class MidpointBudgetPolicy:
    """Small, serializable genotype for recursive midpoint allocation.

    Budget units currently mean seconds requested from a mechanical worker. The
    broker charges the full grant conservatively even when a worker returns
    early; measured wall time is retained in the event trace for later models.
    """

    total_budget: float
    initial_grant: float = 2.5
    grant_growth: float = 2.0
    max_grant: float = 10.0
    max_grants_per_task: int = 3
    attain_priority: float = 1.0
    consume_priority: float = 1.2
    goal_priority: float = 1.1
    relevance_weight: float = 0.35
    reuse_weight: float = 0.25
    exploration_weight: float = 0.30
    progress_weight: float = 0.40
    companion_success_weight: float = 1.25
    failure_penalty: float = 0.15
    tie_break_weight: float = 0.001
    seed: int = 0

    @classmethod
    def from_mapping(
        cls,
        value: Any = None,
        *,
        candidate_count: int = 1,
        requested_total: Any = None,
    ) -> "MidpointBudgetPolicy":
        raw = dict(value) if isinstance(value, dict) else {}
        default_total = max(10.0, 10.0 * (max(1, min(5, candidate_count)) + 1))
        total = raw.get("total_budget", raw.get("total", requested_total))
        total_budget = _clamped_float(total, default_total, 1.0, 600.0)
        initial = _clamped_float(
            raw.get("initial_grant", raw.get("minimum_grant")),
            2.5,
            0.1,
            min(60.0, total_budget),
        )
        max_grant = _clamped_float(
            raw.get("max_grant"),
            10.0,
            initial,
            min(120.0, total_budget),
        )
        return cls(
            total_budget=total_budget,
            initial_grant=initial,
            grant_growth=_clamped_float(raw.get("grant_growth", raw.get("growth_factor")), 2.0, 1.0, 4.0),
            max_grant=max_grant,
            max_grants_per_task=_clamped_int(raw.get("max_grants_per_task"), 3, 1, 8),
            attain_priority=_clamped_float(raw.get("attain_priority"), 1.0, 0.0, 10.0),
            consume_priority=_clamped_float(raw.get("consume_priority"), 1.2, 0.0, 10.0),
            goal_priority=_clamped_float(raw.get("goal_priority"), 1.1, 0.0, 10.0),
            relevance_weight=_clamped_float(raw.get("relevance_weight"), 0.35, 0.0, 10.0),
            reuse_weight=_clamped_float(raw.get("reuse_weight"), 0.25, 0.0, 10.0),
            exploration_weight=_clamped_float(raw.get("exploration_weight"), 0.30, 0.0, 10.0),
            progress_weight=_clamped_float(raw.get("progress_weight"), 0.40, 0.0, 10.0),
            companion_success_weight=_clamped_float(raw.get("companion_success_weight"), 1.25, 0.0, 10.0),
            failure_penalty=_clamped_float(raw.get("failure_penalty"), 0.15, 0.0, 10.0),
            tie_break_weight=_clamped_float(raw.get("tie_break_weight"), 0.001, 0.0, 1.0),
            seed=_clamped_int(raw.get("seed"), 0, 0, 2**31 - 1),
        )

    def to_mapping(self) -> dict[str, Any]:
        return {
            "total_budget": self.total_budget,
            "initial_grant": self.initial_grant,
            "grant_growth": self.grant_growth,
            "max_grant": self.max_grant,
            "max_grants_per_task": self.max_grants_per_task,
            "attain_priority": self.attain_priority,
            "consume_priority": self.consume_priority,
            "goal_priority": self.goal_priority,
            "relevance_weight": self.relevance_weight,
            "reuse_weight": self.reuse_weight,
            "exploration_weight": self.exploration_weight,
            "progress_weight": self.progress_weight,
            "companion_success_weight": self.companion_success_weight,
            "failure_penalty": self.failure_penalty,
            "tie_break_weight": self.tie_break_weight,
            "seed": self.seed,
        }

    @property
    def policy_id(self) -> str:
        encoded = json.dumps(self.to_mapping(), sort_keys=True, separators=(",", ":")).encode("utf-8")
        return f"midpoint_budget_v1_{zlib.crc32(encoded) & 0xFFFFFFFF:08x}"


@dataclass
class BudgetWorkItem:
    task_id: str
    base_score: float
    metadata: dict[str, Any] = field(default_factory=dict)
    enabled: bool = True
    status: str = "ready"
    grant_count: int = 0
    committed_budget: float = 0.0
    failures: int = 0
    progress: float = 0.0
    companion_succeeded: bool = False
    last_context_version: int = -1


class RenewableBudgetBroker:
    """Deterministic request/grant broker with geometric renewable leases."""

    def __init__(self, policy: MidpointBudgetPolicy):
        self.policy = policy
        self.tasks: dict[str, BudgetWorkItem] = {}
        self.events: list[dict[str, Any]] = []
        self.committed_budget = 0.0
        self.context_version = 0

    def register(
        self,
        task_id: str,
        *,
        base_score: float,
        metadata: dict[str, Any] | None = None,
        enabled: bool = True,
    ) -> None:
        if task_id in self.tasks:
            raise ValueError(f"duplicate budget task: {task_id}")
        self.tasks[task_id] = BudgetWorkItem(
            task_id=task_id,
            base_score=float(base_score),
            metadata=dict(metadata or {}),
            enabled=enabled,
        )

    @property
    def remaining_budget(self) -> float:
        return max(0.0, self.policy.total_budget - self.committed_budget)

    def advance_context(self) -> int:
        self.context_version += 1
        self.events.append({
            "event": "context_advanced",
            "context_version": self.context_version,
        })
        return self.context_version

    def update(
        self,
        task_id: str,
        *,
        enabled: bool | None = None,
        companion_succeeded: bool | None = None,
        base_score: float | None = None,
    ) -> None:
        task = self.tasks[task_id]
        if enabled is not None:
            task.enabled = enabled
        if companion_succeeded is not None:
            task.companion_succeeded = companion_succeeded
        if base_score is not None:
            task.base_score = float(base_score)

    def _tie_break(self, task_id: str) -> float:
        encoded = f"{self.policy.seed}:{task_id}".encode("utf-8")
        return ((zlib.crc32(encoded) & 0xFFFFFFFF) / 0xFFFFFFFF) * self.policy.tie_break_weight

    def score(self, task: BudgetWorkItem) -> float:
        exploration = self.policy.exploration_weight / ((1.0 + task.grant_count) ** 0.5)
        return (
            task.base_score
            + exploration
            + self.policy.progress_weight * task.progress
            + (self.policy.companion_success_weight if task.companion_succeeded else 0.0)
            - self.policy.failure_penalty * task.failures
            + self._tie_break(task.task_id)
        )

    def _eligible(self, task: BudgetWorkItem) -> bool:
        if not task.enabled or task.status in {"succeeded", "refuted", "cancelled"}:
            return False
        if task.grant_count == 0:
            return True
        if task.grant_count < self.policy.max_grants_per_task:
            return True
        return task.last_context_version < self.context_version

    def next_grant(self) -> tuple[BudgetWorkItem, float] | None:
        if self.remaining_budget <= 1e-9:
            return None
        eligible = [task for task in self.tasks.values() if self._eligible(task)]
        if not eligible:
            return None
        unstarted = [task for task in eligible if task.grant_count == 0]
        pool = unstarted or eligible
        task = max(pool, key=lambda item: (self.score(item), -len(item.task_id), item.task_id))
        requested = min(
            self.policy.max_grant,
            self.policy.initial_grant * (self.policy.grant_growth ** task.grant_count),
        )
        grant = min(requested, self.remaining_budget)
        if grant <= 1e-9:
            return None
        score = self.score(task)
        task.grant_count += 1
        task.committed_budget += grant
        task.last_context_version = self.context_version
        self.committed_budget += grant
        self.events.append({
            "event": "grant",
            "task_id": task.task_id,
            "leg": task.metadata.get("leg"),
            "candidate": task.metadata.get("candidate"),
            "grant": round(grant, 6),
            "grant_index": task.grant_count,
            "score": round(score, 6),
            "context_version": self.context_version,
            "committed_total": round(self.committed_budget, 6),
            "remaining": round(self.remaining_budget, 6),
        })
        return task, grant

    def report(
        self,
        task_id: str,
        outcome: str,
        *,
        progress: float = 0.0,
        elapsed_seconds: float | None = None,
        detail: Any = None,
    ) -> None:
        task = self.tasks[task_id]
        task.progress = max(0.0, min(1.0, float(progress)))
        if outcome in {"succeeded", "refuted", "cancelled"}:
            task.status = outcome
        else:
            task.status = "retryable"
            task.failures += 1
        event: dict[str, Any] = {
            "event": "report",
            "task_id": task.task_id,
            "outcome": task.status,
            "progress": round(task.progress, 6),
            "context_version": self.context_version,
        }
        if elapsed_seconds is not None:
            event["elapsed_seconds"] = round(max(0.0, elapsed_seconds), 6)
        if detail is not None:
            event["detail"] = detail
        self.events.append(event)

    def snapshot(self) -> dict[str, Any]:
        return {
            "kind": "renewable_budget_broker",
            "policy_id": self.policy.policy_id,
            "policy": self.policy.to_mapping(),
            "committed_budget": round(self.committed_budget, 6),
            "remaining_budget": round(self.remaining_budget, 6),
            "context_version": self.context_version,
            "tasks": [
                {
                    "task_id": task.task_id,
                    "status": task.status,
                    "enabled": task.enabled,
                    "grant_count": task.grant_count,
                    "committed_budget": round(task.committed_budget, 6),
                    "failures": task.failures,
                    "progress": round(task.progress, 6),
                    "companion_succeeded": task.companion_succeeded,
                    **task.metadata,
                }
                for task in self.tasks.values()
            ],
            "events": list(self.events),
        }


# Term algebra

Term = tuple


@dataclass
class UniversalEquation:
    name: str
    eq: dict[str, Any]
    extra_args: list[tuple[str, ...]]
    seed_args: list[tuple[str, ...]] | None = None
    use_args: list[tuple[str, ...]] | None = None

    def as_lemma(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "eq": self.eq,
            "extra_args": self.use_args if self.use_args is not None else self.extra_args,
        }

    def proof_extra_args(self) -> list[tuple[str, ...]]:
        return self.seed_args if self.seed_args is not None else self.extra_args


TOOL_REGISTRY: dict[str, dict[str, Any]] = {
    "forward_saturation": {
        "domain": "true",
        "scope": "both",
        "cost": "medium",
        "feedback_quality": "rich",
        "native_import": "collaborative",
        "aliases": ["saturation", "h_graph", "hargs"],
        "description": "Generate h-instantiations by bounded forward saturation and hand them to Lean/grind.",
    },
    "right_square_chain": {
        "domain": "true",
        "scope": "whole_goal",
        "cost": "cheap",
        "feedback_quality": "basic",
        "native_import": "collab_focused",
        "aliases": ["right_square_absorb", "square_absorb_chain", "right_square_absorption"],
        "description": "Prove/use square_absorb and right_square helper equations.",
    },
    "square_sandwich_chain": {
        "domain": "true",
        "scope": "whole_goal",
        "cost": "cheap",
        "feedback_quality": "basic",
        "native_import": "collab_focused",
        "aliases": ["square_chain", "sandwich_chain", "square_witness_chain"],
        "description": "Prove/use square_const, right_id_square, sandwich, and left_sandwich helpers.",
    },
    "helper_chain_portfolio": {
        "domain": "true",
        "scope": "both",
        "cost": "medium",
        "feedback_quality": "rich",
        "native_import": "collab_protocol",
        "aliases": ["standard_helper_chains", "helper_portfolio", "chain_portfolio"],
        "description": "Try a small portfolio of reusable helper lemma chains through the generic midpoint-chain consumer.",
    },
    "rowconst_certificates": {
        "domain": "true",
        "scope": "whole_goal",
        "cost": "cheap",
        "feedback_quality": "basic",
        "native_import": "native_focused",
        "aliases": ["rowconst_certificate", "explicit_rowconst"],
        "description": "Try focused row-constant certificates.",
    },
    "grounding_derived": {
        "domain": "true",
        "scope": "whole_goal",
        "cost": "cheap",
        "feedback_quality": "structured",
        "native_import": "native_focused",
        "aliases": ["grounding_certificates", "derived_grounding", "cert_ground_derived"],
        "description": "Try the square-rowconst grounding-derived explicit closer.",
    },
    "broad_grounding_derived": {
        "domain": "true",
        "scope": "whole_goal",
        "cost": "medium",
        "feedback_quality": "structured",
        "native_import": "native_certificate",
        "aliases": ["grounding_cert", "broad_grounding_certificates", "cert_grounding_broad"],
        "description": "Try broad proof-carrying grounding certificates by deriving collapse or factor-irrelevance helpers.",
    },
    "collapse_certificates": {
        "domain": "true",
        "scope": "whole_goal",
        "cost": "medium",
        "feedback_quality": "structured",
        "native_import": "native_certificate",
        "aliases": ["collapse_cert", "carrier_collapse", "trivial_magma_cert"],
        "description": "Try proof-carrying collapse certificates: derive a variable-freeing equation and close the goal by carrier collapse.",
    },
    "proof_battery": {
        "domain": "true",
        "scope": "whole_goal",
        "cost": "medium",
        "feedback_quality": "structured",
        "native_import": "native_graph",
        "aliases": ["battery", "old_battery", "deterministic_battery"],
        "description": "Try old battery h-instance layers with an explicit h-fact graph consumer first.",
    },
    "grounding_h": {
        "domain": "true",
        "scope": "whole_goal",
        "cost": "medium",
        "feedback_quality": "structured",
        "native_import": "native_certificate",
        "aliases": ["grounding_h_certificates", "nonorientable_grounding"],
        "description": "Ground the exclusive variables on both sides of a non-orientable H and emit judgeable collapse certificates.",
    },
    "deep_saturation": {
        "domain": "true",
        "scope": "whole_goal",
        "cost": "medium",
        "feedback_quality": "structured",
        "native_import": "native_saturation",
        "aliases": ["saturation_certificates", "bounded_saturation"],
        "description": "Grow a bounded pool from goal subterms, instantiate H in several slots, and close with a Lean-checked grind certificate.",
    },
    "lemma_hint": {
        "domain": "true",
        "scope": "both",
        "cost": "medium",
        "feedback_quality": "rich",
        "native_import": "collab_protocol",
        "aliases": ["lemma", "midpoint", "midpoint_hint", "bridge_lemma"],
        "description": "Prove and consume one or more untrusted bridge equations.",
    },
    "lemma_chain": {
        "domain": "true",
        "scope": "both",
        "cost": "medium",
        "feedback_quality": "rich",
        "native_import": "collab_protocol",
        "aliases": ["chain", "helper_chain", "lemma_sequence"],
        "description": "Prove and consume an ordered sequence of helper equations.",
    },
    "goal_superposition": {
        "domain": "true",
        "scope": "both",
        "cost": "expensive",
        "feedback_quality": "rich",
        "native_import": "native_superposition",
        "aliases": ["superposition", "proof_carrying_superposition", "paramodulation"],
        "description": "Run bounded proof-carrying superposition as a broad true-side consumer.",
    },
    "standard_aux_superposition": {
        "domain": "true",
        "scope": "both",
        "cost": "medium",
        "feedback_quality": "rich",
        "native_import": "native_superposition",
        "aliases": ["aux_superposition", "standard_aux", "collapse_lemmas", "projection_lemmas"],
        "description": "Try standard auxiliary lemmas such as const, projections, and rowconst via proof-carrying superposition.",
    },
    "false_model_search": {
        "domain": "false",
        "scope": "whole_goal",
        "cost": "expensive",
        "feedback_quality": "rich",
        "native_import": "native_false_routes",
        "aliases": ["countermodel_search", "finite_model_search", "local_search", "model_finder", "model_finder_v2", "poly_ce", "cp_sat", "sympy_sat", "structured_ce", "skew_product"],
        "description": "Search for finite countermodels. Supports deterministic families, local/propagation search, exact CP-SAT, polynomial routes, and compact quotient-by-fiber skew products.",
    },
    "false_model_family": {
        "domain": "false",
        "scope": "whole_goal",
        "cost": "medium",
        "feedback_quality": "rich",
        "native_import": "collab_protocol",
        "aliases": ["symbolic_countermodel", "symbolic_model", "finite_model_family"],
        "description": "Expand and verify an LLM-proposed finite symbolic operation family, returning exact H/G near-miss diagnostics or a finite certificate.",
    },
    "infinite_model_artifact": {
        "domain": "false",
        "scope": "whole_goal",
        "cost": "expensive",
        "feedback_quality": "judge_exact",
        "native_import": "collab_protocol",
        "deployability": "policy_sensitive",
        "aliases": [
            "infinite_model",
            "infinite_countermodel",
            "type_level_model",
            "symbolic_type_model",
            "symbolic_model_plan",
        ],
        "description": (
            "Submit a complete or structured Lean Type-level countermodel. The "
            "carrier may be a compact symbolic finite type or an infinite type."
        ),
    },
}

TOOL_ALIASES = {
    alias: name
    for name, spec in TOOL_REGISTRY.items()
    for alias in [name, *spec.get("aliases", [])]
}

TOOL_CONTRACT_FIELDS = ("domain", "scope", "cost", "feedback_quality", "native_import", "deployability")


# Research-layer semantics.  Most competition rows do not yet have an audited
# finite/general classification, so absence from this table deliberately means
# "unknown", not "ordinary false".  These two entries are the first regression
# fixtures for the curriculum described in docs/research_curriculum_plan.md.
KNOWN_IMPLICATION_SEMANTICS: dict[tuple[int, int], dict[str, Any]] = {
    (1167, 1763): {
        "semantic_class": "austin_implication",
        "semantic_target": "general_implication",
        "general_status": "false",
        "finite_status": "true",
        "certificate_class": "infinite_model",
        "source": "ETP Austin-pair classification",
        "source_commit": "df8184f8ae59c71d6f5463b71682d871823a779c",
        "source_registry_sha256": "38d357e116a578cd6654908c0346b4c6ee70dc801ab0a9b542a604206d926c11",
        "note": "Every finite 1167-magma satisfies E1763, but the unrestricted implication is false.",
    },
    (677, 255): {
        "semantic_class": "open_finite_implication",
        "semantic_target": "finite_implication",
        "general_status": "false",
        "finite_status": "unknown",
        "certificate_class": "finite_model_or_finite_structure_proof",
        "source": "ETP Equation 677 chapter",
        "note": "The unrestricted implication is false; whether E677 implies E255 in every finite magma is open.",
    },
}


def implication_semantics(problem: dict[str, Any]) -> dict[str, Any]:
    """Return an explicit finite/general status without guessing missing facts."""
    try:
        key = (int(problem.get("eq1_id")), int(problem.get("eq2_id")))
    except (TypeError, ValueError):
        key = (-1, -1)
    known = KNOWN_IMPLICATION_SEMANTICS.get(key)
    answer = problem.get("answer")
    general_from_row = "true" if answer is True else "false" if answer is False else "unknown"
    out: dict[str, Any] = {
        "eq1_id": None if key[0] < 0 else key[0],
        "eq2_id": None if key[1] < 0 else key[1],
        "semantic_class": "unclassified",
        "semantic_target": "general_implication",
        "general_status": general_from_row,
        "finite_status": "unknown",
        "certificate_class": "finite_model",
        "competition_policy": "prose_finite_vs_judge_general",
        "current_solver_false_artifacts": ["finite_table", "llm_infinite_model_artifact"],
        "research_solver_false_artifacts": ["finite_table", "infinite_model_artifact"],
        "source": "competition row only",
    }
    if known:
        out.update(known)
    if out["general_status"] == "false" and out["finite_status"] == "true":
        out["judge_certificate_status"] = "expressible_as_infinite_lean_model"
        out["current_solver_certificate_status"] = "requires_infinite_model_artifact"
        out["certificate_policy_conflict"] = (
            "The Stage 2 prose requests a finite false witness, while the executable Lean "
            "goal permits an infinite Type-level countermodel. The solver blocks doomed finite "
            "countermodel search and may ask System 2 for a complete Lean infinite-model artifact; "
            "the judge remains the trust boundary."
        )
    else:
        out["judge_certificate_status"] = "potentially_expressible"
        out["current_solver_certificate_status"] = "potentially_supported"
    return out


def finite_countermodel_search_allowed(semantic_context: dict[str, Any] | None) -> bool:
    """A proved finite implication is a hard stop for every finite-model route."""
    return not semantic_context or semantic_context.get("finite_status") != "true"


def semantic_status_state(semantic_context: dict[str, Any]) -> dict[str, Any]:
    finite_status = semantic_context.get("finite_status", "unknown")
    general_status = semantic_context.get("general_status", "unknown")
    if finite_status == "true" and general_status == "false":
        status = "finite_search_prohibited"
        need_hint = (
            "Do not spend more compute on finite countermodels. For unrestricted research, "
            "seek an infinite symbolic model. The Lean judge goal and the structured type-model "
            "adapter can express it without an operation table; finite models are semantically "
            "impossible here."
        )
        actions = [
            {
                "kind": "symbolic_model_plan",
                "representation": "infinite",
                "task": "construct_infinite_countermodel",
                "certificate_class": "infinite_model",
            },
            {
                "kind": "research_task",
                "task": "derive_symbolic_construction_constraints",
                "certificate_class": "infinite_model",
            },
        ]
        representation_plan = {
            "selected": "infinite_symbolic",
            "hard_constraints": [
                "finite_table_prohibited",
                "finite_symbolic_model_prohibited",
            ],
            "allowed_actions": [
                "symbolic_model_plan",
                "symbolic_model_patch",
                "infinite_model_artifact",
            ],
            "reason": "Audited finite implication plus unrestricted refutation.",
        }
    elif finite_status == "unknown" and general_status == "false":
        status = "finite_implication_open"
        need_hint = (
            "General non-implication is known, but finite status is open. Search for finite "
            "countermodels, symbolic finite models, and infinite models as separately "
            "attributed branches."
        )
        actions = [
            {"kind": "research_task", "task": "search_finite_countermodel"},
            {
                "kind": "symbolic_model_plan",
                "representation": "symbolic_finite",
                "task": "construct_formula_defined_finite_countermodel",
            },
            {"kind": "research_task", "task": "derive_finite_structure_theorem"},
        ]
        representation_plan = {
            "selected": "bounded_finite_then_symbolic",
            "hard_constraints": [],
            "allowed_actions": [
                "false_model_search",
                "false_model_family",
                "symbolic_model_plan",
                "infinite_model_artifact",
            ],
            "reason": "Finite status is not known; keep finite and unrestricted branches distinct.",
        }
    else:
        status = "classified" if semantic_context.get("semantic_class") != "unclassified" else "unclassified"
        need_hint = "Treat finite and unrestricted status as unknown unless an audited registry entry says otherwise."
        actions = []
        representation_plan = {
            "selected": "ordinary_portfolio",
            "hard_constraints": [],
            "allowed_actions": [
                "false_model_search",
                "false_model_family",
                "symbolic_model_plan",
            ],
            "reason": "No audited semantic restriction selects a unique carrier class.",
        }
    return protocol_state(
        "SemanticStatus",
        status,
        "semantic_registry",
        semantics=semantic_context,
        representation_plan=representation_plan,
        need_hint=need_hint,
        suggested_next_actions=actions or None,
    )


# A capability mask is an experimental intervention, not a performance flag.
# Each tool has its own switch; composite tools also name the primitive they
# depend on so negative controls can remove both a shortcut and its substitute.
CAPABILITY_DEPENDENCIES: dict[str, list[str]] = {
    "lemma_hint": ["primitive:generic_midpoint_prover"],
    "lemma_chain": ["primitive:generic_midpoint_prover"],
    "helper_chain_portfolio": ["primitive:generic_midpoint_prover"],
    "goal_superposition": ["primitive:proof_carrying_superposition"],
    "standard_aux_superposition": ["primitive:proof_carrying_superposition"],
    "false_model_search": ["primitive:finite_model_search"],
    "false_model_family": ["primitive:symbolic_family_evaluator", "primitive:finite_model_search"],
    "infinite_model_artifact": ["artifact:infinite_model", "primitive:lean_verifier"],
}

PRIMITIVE_CAPABILITIES: dict[str, dict[str, Any]] = {
    "primitive:generic_midpoint_prover": {
        "kind": "primitive",
        "description": "Prove proposed universal bridge equations and consume them toward the goal.",
    },
    "primitive:proof_carrying_superposition": {
        "kind": "primitive",
        "description": "Bounded superposition that preserves a renderable proof trace.",
    },
    "primitive:finite_model_search": {
        "kind": "primitive",
        "description": "Finite-table countermodel routes and validation.",
    },
    "primitive:symbolic_family_evaluator": {
        "kind": "primitive",
        "description": "Validate compact finite operation schemas, expand them to tables, and report universal H/G diagnostics.",
    },
    "primitive:lean_verifier": {
        "kind": "verifier",
        "description": "Trusted Lean verification; never withheld in curriculum experiments.",
    },
    "artifact:infinite_model": {
        "kind": "artifact",
        "description": "Complete Lean code defining an infinite magma and proving H plus failure of the goal.",
    },
}


def normalize_capability_mask(mask: Any = None) -> dict[str, list[str]]:
    if mask is None:
        disabled: list[str] = []
    elif isinstance(mask, dict):
        disabled = [str(item) for item in mask.get("disabled", [])]
    elif isinstance(mask, (list, tuple, set)):
        disabled = [str(item) for item in mask]
    else:
        disabled = [str(mask)]
    return {"disabled": sorted(set(disabled))}


def required_capabilities_for_tool(tool: Any) -> list[str]:
    name = TOOL_ALIASES.get(str(tool or "").strip(), str(tool or "").strip())
    return [f"tool:{name}", *CAPABILITY_DEPENDENCIES.get(name, [])]


def capability_tool_for_action(action: dict[str, Any]) -> str:
    raw = str(action.get("tool") or action.get("kind") or "").strip()
    if raw in {"midpoint_chain", "lemma_chain"}:
        return "lemma_chain"
    if raw in {"midpoint", "lemma_hint"}:
        return "lemma_hint"
    return TOOL_ALIASES.get(raw, raw)


def capability_gate_state(tool: Any, mask: Any = None) -> dict[str, Any] | None:
    normalized = normalize_capability_mask(mask)
    required = required_capabilities_for_tool(tool)
    blocked = [capability for capability in required if capability in normalized["disabled"]]
    if not blocked:
        return None
    name = TOOL_ALIASES.get(str(tool or "").strip(), str(tool or "").strip())
    return protocol_state(
        "CapabilityWithheldState",
        "withheld_for_curriculum",
        "capability_mask",
        tool=name,
        required_capabilities=required,
        blocked_capabilities=blocked,
        capability_mask=normalized,
        need_hint="Choose a route whose required capabilities remain available; the withheld route is an experimental intervention.",
    )


def capability_manifest(mask: Any = None) -> dict[str, Any]:
    normalized = normalize_capability_mask(mask)
    disabled = set(normalized["disabled"])
    tools = []
    for name, spec in TOOL_REGISTRY.items():
        required = required_capabilities_for_tool(name)
        tools.append({
            "capability": f"tool:{name}",
            "tool": name,
            "kind": "tool",
            "domain": spec.get("domain"),
            "required_capabilities": required,
            "available": not any(capability in disabled for capability in required),
            "description": spec.get("description"),
        })
    primitives = [
        {"capability": name, **spec, "available": name not in disabled}
        for name, spec in PRIMITIVE_CAPABILITIES.items()
    ]
    return {"mask": normalized, "tools": tools, "primitives": primitives}


def tool_contract(tool: Any) -> dict[str, Any] | None:
    """Return the protocol-visible contract for a tool registry entry."""
    name = TOOL_ALIASES.get(str(tool or "").strip(), str(tool or "").strip())
    spec = TOOL_REGISTRY.get(name)
    if not spec:
        return None
    return {
        "tool": name,
        "capability": f"tool:{name}",
        "required_capabilities": required_capabilities_for_tool(name),
        **{field: spec[field] for field in TOOL_CONTRACT_FIELDS if field in spec},
    }


def normalize(text: str) -> str:
    return text.replace("*", "◇") if isinstance(text, str) else text


def variables_of(text: str) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for v in re.findall(r"\b([a-z][a-z0-9_]*)\b", text):
        if v not in seen:
            seen.add(v)
            out.append(v)
    return out


def strip_outer(s: str) -> str:
    s = s.strip()
    while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
        depth = 0
        wraps = True
        for i, c in enumerate(s):
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
            if depth == 0 and i < len(s) - 1:
                wraps = False
                break
        if not wraps:
            break
        s = s[1:-1].strip()
    return s


def parse_term(text: str, variables: set[str]) -> Term:
    s = strip_outer(normalize(text))
    depth = 0
    last_op = -1
    for i, c in enumerate(s):
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        elif c == "◇" and depth == 0:
            last_op = i
    if last_op >= 0:
        return ("op", parse_term(s[:last_op], variables), parse_term(s[last_op + 1 :], variables))
    if s in variables:
        return ("var", s)
    raise ValueError(f"cannot parse term: {text!r}")


def parse_equation(text: str) -> dict[str, Any]:
    text = normalize(text)
    lhs_s, rhs_s = [p.strip() for p in text.split("=", 1)]
    vs = variables_of(text)
    vset = set(vs)
    lhs = parse_term(lhs_s, vset)
    rhs = parse_term(rhs_s, vset)
    return {
        "text": f"{term_to_str(lhs)} = {term_to_str(rhs)}",
        "variables": vs,
        "lhs": lhs,
        "rhs": rhs,
    }


def term_to_str(t: Term) -> str:
    if t[0] == "var":
        return t[1]
    return f"({term_to_str(t[1])} ◇ {term_to_str(t[2])})"


def term_to_str_subst(t: Term, subst: dict[str, str]) -> str:
    if t[0] == "var":
        return subst.get(t[1], t[1])
    return f"({term_to_str_subst(t[1], subst)} ◇ {term_to_str_subst(t[2], subst)})"


def subterms(t: Term) -> list[Term]:
    if t[0] == "var":
        return [t]
    return [t] + subterms(t[1]) + subterms(t[2])


def term_variables(t: Term) -> list[str]:
    if t[0] == "var":
        return [t[1]]
    return unique(term_variables(t[1]) + term_variables(t[2]))


def term_var_count(t: Term, var: str) -> int:
    if t[0] == "var":
        return 1 if t[1] == var else 0
    return term_var_count(t[1], var) + term_var_count(t[2], var)


def term_leaf_sequence(t: Term) -> tuple[str, ...]:
    if t[0] == "var":
        return (t[1],)
    return term_leaf_sequence(t[1]) + term_leaf_sequence(t[2])


def term_occurrence_signature(t: Term, modulus: int | None = None) -> tuple[tuple[str, int], ...]:
    counts = Counter(term_leaf_sequence(t))
    if modulus is None:
        return tuple(sorted((var, int(count)) for var, count in counts.items()))
    return tuple(sorted(
        (var, int(count) % modulus)
        for var, count in counts.items()
        if int(count) % modulus
    ))


def term_left_path_depth(t: Term) -> int:
    return 0 if t[0] == "var" else 1 + term_left_path_depth(t[1])


def term_right_path_depth(t: Term) -> int:
    return 0 if t[0] == "var" else 1 + term_right_path_depth(t[2])


def equation_signature_holds(eq: dict[str, Any], signature) -> bool:
    return signature(eq["lhs"]) == signature(eq["rhs"])


def symbolic_invariant_report(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
) -> list[dict[str, Any]]:
    """Stage-1-style strict witnesses exposed as finite family routing facts."""
    rows: list[dict[str, Any]] = []
    seen_actions: set[str] = set()

    def add(
        family: str,
        signature,
        action: dict[str, Any] | None,
        reason: str,
    ) -> None:
        h_holds = equation_signature_holds(h_eq, signature)
        if not h_holds:
            return
        g_holds = equation_signature_holds(g_eq, signature)
        action_key = json.dumps(action, sort_keys=True) if action is not None else family
        if action_key in seen_actions:
            return
        seen_actions.add(action_key)
        rows.append({
            "family": family,
            "h_holds": True,
            "g_holds": g_holds,
            "separates_goal": not g_holds,
            "reason": reason,
            "action": action,
        })

    add(
        "left_projection",
        lambda term: term_leaf_sequence(term)[0],
        {"kind": "false_model_family", "carrier_size": 2, "default": {"kind": "left"}, "budget": 3},
        "terms evaluate to their leftmost leaf",
    )
    add(
        "right_projection",
        lambda term: term_leaf_sequence(term)[-1],
        {"kind": "false_model_family", "carrier_size": 2, "default": {"kind": "right"}, "budget": 3},
        "terms evaluate to their rightmost leaf",
    )
    add(
        "set_semilattice",
        lambda term: frozenset(term_leaf_sequence(term)),
        {"kind": "false_model_family", "carrier_size": 2, "default": {"kind": "max"}, "budget": 3},
        "the two-element join semilattice evaluates a term by the set of variables assigned 1",
    )
    add(
        "free_semigroup_leaf_sequence",
        term_leaf_sequence,
        None,
        "H preserves exact leaf order; a finite semigroup quotient may separate a different goal word",
    )
    for modulus in (2, 3, 5, 7):
        add(
            f"occurrence_counts_mod_{modulus}",
            lambda term, modulus=modulus: term_occurrence_signature(term, modulus),
            {
                "kind": "false_model_family",
                "carrier_size": modulus,
                "default": {"kind": "affine", "params": [1, 1, 0]},
                "budget": 3,
            },
            f"addition modulo {modulus} evaluates occurrence-count vectors",
        )
    add(
        "left_successor_mod_3",
        lambda term: (term_leaf_sequence(term)[0], term_left_path_depth(term) % 3),
        {"kind": "false_model_family", "carrier_size": 3, "default": {"kind": "left_successor"}, "budget": 3},
        "a ◇ b = a+1 mod 3 tracks the leftmost variable and left-path depth",
    )
    add(
        "right_successor_mod_3",
        lambda term: (term_leaf_sequence(term)[-1], term_right_path_depth(term) % 3),
        {"kind": "false_model_family", "carrier_size": 3, "default": {"kind": "right_successor"}, "budget": 3},
        "a ◇ b = b+1 mod 3 tracks the rightmost variable and right-path depth",
    )
    rows.sort(key=lambda row: (not row["separates_goal"], row["family"]))
    return rows[:8]


def one_sided_variables(eq: dict[str, Any]) -> list[str]:
    lhs_vars = set(term_variables(eq["lhs"]))
    rhs_vars = set(term_variables(eq["rhs"]))
    return [v for v in eq["variables"] if (v in lhs_vars) != (v in rhs_vars)]


def unique(items: list[Any]) -> list[Any]:
    out: list[Any] = []
    seen: set[Any] = set()
    for x in items:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out


def unique_arg_rows(rows: list[tuple[str, ...]]) -> list[tuple[str, ...]]:
    out: list[tuple[str, ...]] = []
    seen: set[tuple[str, ...]] = set()
    for row in rows:
        tup = tuple(row)
        if tup not in seen:
            seen.add(tup)
            out.append(tup)
    return out


def lean_arg(text: str) -> str:
    text = text.strip()
    if ("◇" in text or " " in text) and not (text.startswith("(") and text.endswith(")")):
        return f"({text})"
    return text


# Lean wrappers


def indent(body: str, spaces: int = 2) -> str:
    prefix = " " * spaces
    return "\n".join(prefix + ln if ln.strip() else ln for ln in body.splitlines())


def make_true_code(body: str) -> str:
    return (
        "import JudgeProblem\n\n"
        "set_option maxHeartbeats 12800000 in\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        f"{indent(clean_body(body), 2)}\n"
    )


def table_expr_formula(table: list[list[int]]) -> str:
    n = len(table)

    def row_expr(i: int) -> str:
        expr = str(table[i][-1])
        for j in range(n - 2, -1, -1):
            expr = f"if j.val = {j} then {table[i][j]} else ({expr})"
        return expr

    expr = row_expr(n - 1)
    for i in range(n - 2, -1, -1):
        expr = f"if i.val = {i} then ({row_expr(i)}) else ({expr})"
    return f"Nat.mod ({expr}) {n}"


def make_false_code(n: int, table: list[list[int]]) -> str:
    if n <= 10 and all(0 <= int(value) <= 9 for row in table for value in row):
        return (
            "import JudgeProblem\n"
            "import JudgeDecide.DecideBang\n"
            "import JudgeFinOp.MemoFinOp\n"
            "open MemoFinOp\n\n"
            "set_option maxRecDepth 40000\n"
            "set_option maxHeartbeats 1000000000\n"
            + "def submission : Goal := by\n"
            f"  let m : Magma (Fin {n}) := {{\n"
            f"    op := finOpTable \"{json.dumps(table)}\"\n"
            "  }\n"
            f"  refine ⟨Fin {n}, m, ?_⟩\n"
            "  decideFin!\n"
        )
    op_formula = table_expr_formula(table)
    return make_false_formula_code(n, op_formula)


def make_false_formula_code(n: int, op_formula: str) -> str:
    return (
        "import JudgeProblem\n"
        "import JudgeDecide.DecideBang\n"
        "set_option maxRecDepth 40000\n"
        "set_option maxHeartbeats 1000000000\n"
        "def submission : Goal := by\n"
        f"  let m : Magma (Fin {n}) := {{ op := fun i j =>\n"
        f"    ⟨{op_formula}, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩ }}\n"
        f"  refine ⟨Fin {n}, m, ?_⟩\n"
        "  decideFin!\n"
    )


def clean_body(raw: str) -> str:
    body = raw.strip()
    body = re.sub(r"<think>[\s\S]*?</think>", "", body).strip()
    body = re.sub(r"^```(?:lean)?\s*\n?", "", body)
    body = re.sub(r"\n?```\s*$", "", body)
    body = re.sub(r"^\s*import .*$", "", body, flags=re.MULTILINE)
    body = re.sub(r"^.*def\s+submission\s*:.*?:=\s*by\s*", "", body, flags=re.DOTALL)
    body = re.sub(r"^\s*intro\s+G\s+_\s+h\s*\n?", "", body)
    return normalize(body).strip()


# Countermodel checking/search


def eval_term(t: Term, env: dict[str, int], table: list[list[int]]) -> int:
    if t[0] == "var":
        return env[t[1]]
    return table[eval_term(t[1], env, table)][eval_term(t[2], env, table)]


def eq_holds(eq: dict[str, Any], table: list[list[int]]) -> bool:
    n = len(table)
    for vals in product(range(n), repeat=len(eq["variables"])):
        env = dict(zip(eq["variables"], vals))
        if eval_term(eq["lhs"], env, table) != eval_term(eq["rhs"], env, table):
            return False
    return True


def is_counterexample(h_eq: dict[str, Any], g_eq: dict[str, Any], table: list[list[int]]) -> bool:
    return bool(table) and eq_holds(h_eq, table) and not eq_holds(g_eq, table)


def witness_tables() -> list[list[list[int]]]:
    """Small deterministic witnesses retained independently of any reference solver."""
    return [
        [[0, 0], [1, 1]],
        [[0, 1], [0, 1]],
        [[0, 0], [0, 0]],
        [[0, 1], [1, 0]],
        [[0, 0], [0, 1]],
        [[0, 1], [1, 1]],
        [[1, 0], [0, 1]],
        [[1, 1], [1, 0]],
        [[1, 0], [0, 0]],
        [[1, 0], [1, 1]],
        [[0, 1], [0, 0]],
        [[0, 0], [1, 0]],
        [[0, 1, 2], [1, 2, 0], [2, 0, 1]],
        [[0, 2, 1], [2, 1, 0], [1, 0, 2]],
        [[0, 0, 0], [0, 0, 0], [0, 1, 0]],
        [[0, 0, 0], [0, 0, 0], [0, 0, 1]],
        [[3, 1, 1, 3], [0, 3, 2, 3], [3, 1, 3, 3], [0, 1, 2, 3]],
        [[1, 2, 3, 4, 0], [0, 4, 3, 4, 1], [4, 2, 2, 1, 0], [2, 0, 2, 3, 2], [3, 1, 3, 0, 4]],
        [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [0, 0, 1, 0]],
        [[4, 3, 2, 2, 2], [2, 3, 2, 2, 3], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2]],
        [[0, 0, 0, 2, 2], [4, 1, 1, 4, 1], [1, 2, 2, 1, 2], [2, 3, 3, 3, 2], [2, 4, 4, 2, 4]],
        [[3, 3, 2, 2], [1, 1, 0, 0], [3, 3, 2, 2], [1, 1, 0, 0]],
        [[3, 2, 3, 3], [3, 3, 3, 3], [2, 3, 3, 3], [1, 2, 3, 3]],
        [[2, 2, 2, 3], [3, 3, 2, 3], [2, 2, 2, 3], [3, 3, 2, 3]],
        [[0, 2, 3, 1], [3, 1, 0, 2], [1, 3, 2, 0], [2, 0, 1, 3]],
        [[3, 3, 2, 2, 3], [4, 4, 2, 4, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2]],
    ]


def structured_tables(max_n: int = 6):
    """Source-independent algebraic witness families, with duplicate suppression."""
    seen: set[tuple[tuple[int, ...], ...]] = set()

    def emit(table: list[list[int]]):
        key = tuple(tuple(row) for row in table)
        if key in seen:
            return None
        seen.add(key)
        return table

    for n in range(2, max_n + 1):
        candidates = [
            [[min(i, j) for j in range(n)] for i in range(n)],
            [[max(i, j) for j in range(n)] for i in range(n)],
            [[i for _ in range(n)] for i in range(n)],
            [[j for j in range(n)] for _ in range(n)],
            [[(i + j) % n for j in range(n)] for i in range(n)],
            [[(i - j) % n for j in range(n)] for i in range(n)],
            [[(-i - j) % n for j in range(n)] for i in range(n)],
            [[(1 - i - j) % n for j in range(n)] for i in range(n)],
            [[(i + 1) % n for _ in range(n)] for i in range(n)],
            [[(j + 1) % n for j in range(n)] for _ in range(n)],
            [[j if i == 0 else i for j in range(n)] for i in range(n)],
            [[i if j == 0 else j for j in range(n)] for i in range(n)],
        ]
        for c in range(n):
            candidates.append([[c] * n for _ in range(n)])
            candidates.append([[i if i == j else c for j in range(n)] for i in range(n)])
        for table in candidates:
            item = emit(table)
            if item is not None:
                yield item
    for rows in range(2, max_n + 1):
        for cols in range(2, max_n + 1):
            n = rows * cols
            if n > max_n:
                continue
            table = []
            for left in range(n):
                left_row, _ = divmod(left, cols)
                table.append([(left_row * cols) + (right % cols) for right in range(n)])
            item = emit(table)
            if item is not None:
                yield item


def small_false_search(h_eq: dict[str, Any], g_eq: dict[str, Any], budget: float = 4.0):
    deadline = time.monotonic() + budget
    for table in witness_tables():
        if is_counterexample(h_eq, g_eq, table):
            return len(table), table
    for table in structured_tables(6):
        if time.monotonic() > deadline:
            return None
        if is_counterexample(h_eq, g_eq, table):
            return len(table), table
    # Exhaustive Fin 2 only: cheap and deterministic.
    n = 2
    for enc in range(n ** (n * n)):
        table = [[(enc // (n ** (i * n + j))) % n for j in range(n)] for i in range(n)]
        if is_counterexample(h_eq, g_eq, table):
            return n, table
    return None


def trace_eval(t: Term, env: dict[str, int], table: list[list[int]], touched: list[tuple[int, int]]) -> int:
    if t[0] == "var":
        return env[t[1]]
    a = trace_eval(t[1], env, table, touched)
    b = trace_eval(t[2], env, table, touched)
    touched.append((a, b))
    return table[a][b]


def safe_model_family_expr(text: str, env: dict[str, int]) -> int | bool:
    """Evaluate the deliberately small expression language used by model families."""
    source = str(text).strip().replace("&&", " and ").replace("||", " or ")
    if not source or len(source) > 160:
        raise ValueError("family expression must contain 1..160 characters")
    parsed = ast.parse(source, mode="eval")
    if sum(1 for _ in ast.walk(parsed)) > 80:
        raise ValueError("family expression is too complex")

    def walk(node: ast.AST) -> int | bool:
        if isinstance(node, ast.Expression):
            return walk(node.body)
        if isinstance(node, ast.Constant) and isinstance(node.value, (int, bool)):
            return node.value
        if isinstance(node, ast.Name) and node.id in env:
            return env[node.id]
        if isinstance(node, ast.UnaryOp):
            value = walk(node.operand)
            if isinstance(node.op, ast.USub):
                return -int(value)
            if isinstance(node.op, ast.UAdd):
                return int(value)
            if isinstance(node.op, ast.Not):
                return not bool(value)
        if isinstance(node, ast.BinOp):
            left = int(walk(node.left))
            right = int(walk(node.right))
            if isinstance(node.op, ast.Add):
                return left + right
            if isinstance(node.op, ast.Sub):
                return left - right
            if isinstance(node.op, ast.Mult):
                return left * right
            if isinstance(node.op, ast.FloorDiv):
                if right == 0:
                    raise ValueError("division by zero in family expression")
                return left // right
            if isinstance(node.op, ast.Mod):
                if right == 0:
                    raise ValueError("modulo by zero in family expression")
                return left % right
        if isinstance(node, ast.BoolOp):
            values = [bool(walk(value)) for value in node.values]
            if isinstance(node.op, ast.And):
                return all(values)
            if isinstance(node.op, ast.Or):
                return any(values)
        if isinstance(node, ast.Compare):
            left = int(walk(node.left))
            for op, right_node in zip(node.ops, node.comparators):
                right = int(walk(right_node))
                if isinstance(op, ast.Eq):
                    ok = left == right
                elif isinstance(op, ast.NotEq):
                    ok = left != right
                elif isinstance(op, ast.Lt):
                    ok = left < right
                elif isinstance(op, ast.LtE):
                    ok = left <= right
                elif isinstance(op, ast.Gt):
                    ok = left > right
                elif isinstance(op, ast.GtE):
                    ok = left >= right
                else:
                    raise ValueError("unsupported comparison in family expression")
                if not ok:
                    return False
                left = right
            return True
        raise ValueError(f"unsupported family expression node: {type(node).__name__}")

    return walk(parsed)


def symbolic_family_default_value(spec: Any, i: int, j: int, n: int) -> int:
    if isinstance(spec, str):
        kind = spec.strip().lower()
        params: list[int] = []
    elif isinstance(spec, dict):
        kind = str(spec.get("kind") or spec.get("name") or "right").strip().lower()
        raw_params = spec.get("params") or []
        if not isinstance(raw_params, list) or len(raw_params) > 8:
            raise ValueError("default params must be a list of at most 8 integers")
        params = [int(value) for value in raw_params]
    else:
        raise ValueError("default operation must be a string or object")
    if kind in {"right", "proj_r", "second"}:
        return j % n
    if kind in {"left", "proj_l", "first"}:
        return i % n
    if kind in {"constant", "const"}:
        return (params[0] if params else 0) % n
    if kind == "affine":
        a, b, c = (params + [0, 1, 0])[:3]
        return (a * i + b * j + c) % n
    if kind == "bilinear":
        a, b, c, d = (params + [0, 1, 0, 0])[:4]
        return (a * i + b * j + c * i * j + d) % n
    if kind == "quadratic":
        a, b, c, d, e, f = (params + [0, 1, 0, 0, 0, 0])[:6]
        return (a * i + b * j + c * i * j + d * i * i + e * j * j + f) % n
    if kind == "min":
        return min(i, j)
    if kind == "max":
        return max(i, j)
    if kind in {"left_successor", "succ_left"}:
        return (i + (params[0] if params else 1)) % n
    if kind in {"right_successor", "succ_right"}:
        return (j + (params[0] if params else 1)) % n
    raise ValueError(f"unsupported default operation kind: {kind}")


def symbolic_family_rule_applies(rule: dict[str, Any], i: int, j: int, n: int) -> bool:
    condition = rule.get("when", rule.get("if", rule.get("condition")))
    if isinstance(condition, str):
        return bool(safe_model_family_expr(condition, {"i": i, "j": j, "n": n}))
    if not isinstance(condition, dict):
        raise ValueError("each family rule needs a string or object `when` condition")
    kind = str(condition.get("kind") or "").strip().lower()
    if kind in {"diagonal", "diag"}:
        return i == j
    if kind in {"off_diagonal", "offdiag"}:
        return i != j
    if kind in {"same_mod", "same_residue"}:
        modulus = max(1, int(condition.get("mod") or 2))
        return (i - j) % modulus == 0
    if kind in {"different_mod", "different_residue"}:
        modulus = max(1, int(condition.get("mod") or 2))
        return (i - j) % modulus != 0
    if kind in {"left_residue", "left_mod"}:
        modulus = max(1, int(condition.get("mod") or 2))
        residue = int(condition.get("residue") or 0)
        return i % modulus == residue % modulus
    if kind in {"right_residue", "right_mod"}:
        modulus = max(1, int(condition.get("mod") or 2))
        residue = int(condition.get("residue") or 0)
        return j % modulus == residue % modulus
    if kind in {"cell", "patch"}:
        return i == int(condition.get("i")) and j == int(condition.get("j"))
    raise ValueError(f"unsupported family rule condition: {kind}")


def symbolic_family_rule_value(rule: dict[str, Any], i: int, j: int, n: int) -> int:
    value = rule.get("value", rule.get("then"))
    if isinstance(value, int):
        return value % n
    if isinstance(value, str):
        return int(safe_model_family_expr(value, {"i": i, "j": j, "n": n})) % n
    if isinstance(value, dict):
        return symbolic_family_default_value(value, i, j, n)
    raise ValueError("family rule value must be an integer, expression, or operation object")


def normalize_symbolic_family_payload(data: dict[str, Any]) -> dict[str, Any]:
    source = data.get("family") if isinstance(data.get("family"), dict) else data
    out = dict(source)
    schema_repairs: list[dict[str, Any]] = []
    operation = out.get("operation")
    if isinstance(operation, dict) and any(key in operation for key in ("default", "rules", "patches")):
        if "default" not in out and "default" in operation:
            out["default"] = operation.get("default")
        if "rules" not in out and "rules" in operation:
            out["rules"] = operation.get("rules")
        if "patches" not in out and "patches" in operation:
            out["patches"] = operation.get("patches")
    elif operation is not None and "default" not in out:
        out["default"] = operation
    if "n" in out and "carrier_size" not in out:
        out["carrier_size"] = out.get("n")
    raw_rules = out.get("rules")
    normalized_rules: list[Any] = []
    for index, raw_rule in enumerate(raw_rules if isinstance(raw_rules, list) else []):
        if not isinstance(raw_rule, dict):
            normalized_rules.append(raw_rule)
            continue
        rule = dict(raw_rule)
        condition_key = next(
            (key for key in ("when", "if", "condition") if key in rule),
            "when",
        )
        condition = rule.get(condition_key)
        if isinstance(condition, dict):
            fixed = dict(condition)
            kind = str(fixed.get("kind") or "").strip().lower()
            if kind in {"diagonal", "diag"} and (
                "i" in fixed or "j" in fixed or "value" in fixed
            ):
                diagonal_value = fixed.get("i", fixed.get("j", fixed.get("value", 0)))
                fixed = {
                    "kind": "cell",
                    "i": diagonal_value,
                    "j": diagonal_value,
                }
            elif kind in {"pair", "exact_pair", "point"}:
                if "left" in fixed and "right" in fixed:
                    fixed = {
                        "kind": "cell",
                        "i": fixed.get("left"),
                        "j": fixed.get("right"),
                    }
            elif not kind and "left" in fixed and "right" in fixed:
                fixed = {
                    "kind": "cell",
                    "i": fixed.get("left"),
                    "j": fixed.get("right"),
                }
            elif not kind and "i" in fixed and "j" in fixed:
                fixed["kind"] = "cell"
            elif kind in {"left_eq", "left_value", "row"}:
                value = fixed.get("value", fixed.get("left", fixed.get("i", 0)))
                fixed = f"i == {int(value)}"
            elif kind in {"right_eq", "right_value", "column"}:
                value = fixed.get("value", fixed.get("right", fixed.get("j", 0)))
                fixed = f"j == {int(value)}"
            if fixed != condition:
                schema_repairs.append({
                    "rule_index": index,
                    "field": condition_key,
                    "from": condition,
                    "to": fixed,
                    "reason": "canonicalized_unambiguous_condition_alias",
                })
                rule[condition_key] = fixed
        normalized_rules.append(rule)
    if isinstance(raw_rules, list):
        out["rules"] = normalized_rules
    if schema_repairs:
        out["_schema_repairs"] = schema_repairs
    return out


def table_from_symbolic_family(data: dict[str, Any]) -> tuple[list[list[int]], dict[str, Any]]:
    family = normalize_symbolic_family_payload(data)
    n = int(family.get("carrier_size") or 0)
    if n < 2 or n > 40:
        raise ValueError(f"carrier_size must be in 2..40, got {n}")
    default = family.get("default", {"kind": "right"})
    rules = family.get("rules") or []
    patches = family.get("patches") or []
    if not isinstance(rules, list) or len(rules) > 16:
        raise ValueError("rules must be a list of at most 16 objects")
    if not isinstance(patches, list) or len(patches) > 64:
        raise ValueError("patches must be a list of at most 64 cells")
    table: list[list[int]] = []
    touched: set[tuple[int, int]] = set()
    for i in range(n):
        row: list[int] = []
        for j in range(n):
            value = symbolic_family_default_value(default, i, j, n)
            for rule in rules:
                if not isinstance(rule, dict):
                    raise ValueError("every family rule must be an object")
                if symbolic_family_rule_applies(rule, i, j, n):
                    value = symbolic_family_rule_value(rule, i, j, n)
                    touched.add((i, j))
            row.append(value % n)
        table.append(row)
    for patch in patches:
        if isinstance(patch, (list, tuple)) and len(patch) == 3:
            i, j, value = (int(patch[0]), int(patch[1]), int(patch[2]))
        elif isinstance(patch, dict):
            i, j, value = int(patch["i"]), int(patch["j"]), int(patch["value"])
        else:
            raise ValueError("each patch must be [i,j,value] or an object with i/j/value")
        if not (0 <= i < n and 0 <= j < n):
            raise ValueError(f"patch cell {(i, j)} is outside Fin {n}")
        table[i][j] = value % n
        touched.add((i, j))
    default_summary = (
        default
        if isinstance(default, str)
        else {
            "kind": default.get("kind") or default.get("name"),
            "params": list(default.get("params") or []),
        }
    )
    return table, {
        "carrier_size": n,
        "default": default_summary,
        "rule_count": len(rules),
        "patch_count": len(patches),
        "rule_touched_cells": len(touched),
        "schema_repairs": list(family.get("_schema_repairs") or []),
    }


def symbolic_equation_scan(
    eq: dict[str, Any],
    table: list[list[int]],
    *,
    deadline: float,
    assignment_cap: int,
    violation_cap: int,
) -> dict[str, Any]:
    n = len(table)
    total = n ** len(eq["variables"])
    checked = 0
    failures = 0
    examples: list[dict[str, Any]] = []
    hot_cells: Counter[tuple[int, int]] = Counter()
    stop_reason = "complete"
    for vals in product(range(n), repeat=len(eq["variables"])):
        if checked >= assignment_cap:
            stop_reason = "assignment_cap"
            break
        if time.monotonic() >= deadline:
            stop_reason = "time_budget"
            break
        env = dict(zip(eq["variables"], vals))
        touched: list[tuple[int, int]] = []
        lhs = trace_eval(eq["lhs"], env, table, touched)
        rhs = trace_eval(eq["rhs"], env, table, touched)
        checked += 1
        if lhs == rhs:
            continue
        failures += 1
        hot_cells.update(touched)
        if len(examples) < 5:
            examples.append({
                "env": env,
                "lhs": lhs,
                "rhs": rhs,
                "cells": [list(cell) for cell in unique(touched)[:12]],
            })
        if failures >= violation_cap:
            stop_reason = "violation_cap"
            break
    return {
        "assignments_total": total,
        "assignments_checked": checked,
        "complete": checked == total,
        "failures_observed": failures,
        "stop_reason": stop_reason,
        "examples": examples,
        "hot_cells": [
            {"cell": list(cell), "count": count}
            for cell, count in hot_cells.most_common(8)
        ],
    }


def false_model_family_attempt(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    data: dict[str, Any],
) -> tuple[tuple[int, list[list[int]]] | None, dict[str, Any]]:
    """Expand and fully verify one untrusted finite symbolic model family."""
    budget = max(0.5, min(30.0, float(data.get("budget") or data.get("time_budget") or 8.0)))
    assignment_cap = max(1_000, min(5_000_000, int(data.get("assignment_cap") or 2_000_000)))
    try:
        table, family_summary = table_from_symbolic_family(data)
    except Exception as exc:
        return None, protocol_state(
            "FalseModelFamilyState",
            "invalid_family",
            "false_model_family",
            tool="false_model_family",
            errors=[ProtocolIssue("invalid_family_schema", short_text(str(exc), 500)).to_dict()],
            need_hint="Repair the carrier/default/rules schema. Use only supported compact arithmetic or residue/diagonal conditions.",
        )

    started = time.monotonic()
    h_deadline = started + budget * 0.75
    final_deadline = started + budget
    h_profile = symbolic_equation_scan(
        h_eq,
        table,
        deadline=h_deadline,
        assignment_cap=assignment_cap,
        violation_cap=64,
    )
    g_profile = symbolic_equation_scan(
        g_eq,
        table,
        deadline=final_deadline,
        assignment_cap=assignment_cap,
        violation_cap=8,
    )
    h_holds = bool(h_profile["complete"] and h_profile["failures_observed"] == 0)
    g_fails = bool(g_profile["failures_observed"] > 0)

    if h_holds and g_fails:
        status = "found"
        repair_class = "verified_countermodel"
        need_hint = None
    elif h_profile["failures_observed"] > 0 and g_fails:
        status = "h_violated"
        repair_class = "repair_h_preserve_g"
        need_hint = (
            "The family already breaks G but violates H. Repair the operation regions "
            "listed in h_profile.hot_cells while preserving the G-breaking example."
        )
    elif h_holds and g_profile["complete"]:
        status = "goal_also_holds"
        repair_class = "break_g_preserve_h"
        need_hint = (
            "H holds universally, but G also holds. Add a coherent residue, block, "
            "diagonal, or affine-region change that breaks the displayed goal assignment "
            "without disturbing H."
        )
    elif h_profile["complete"] and h_profile["failures_observed"] > 0:
        status = "h_violated_goal_unbroken"
        repair_class = "repair_h_and_break_g"
        need_hint = (
            "This family violates H and does not yet break G. Prefer a different coherent "
            "family or carrier unless one small repair can both remove the displayed H "
            "violations and create a concrete G-breaking assignment."
        )
    elif not h_profile["complete"]:
        status = "h_check_incomplete"
        repair_class = "reduce_or_symbolically_justify"
        need_hint = (
            "Universal H checking exceeded the bounded assignment/time contract. "
            "Reduce the carrier, simplify the family, or provide a structure whose H law "
            "can later be discharged symbolically."
        )
    else:
        status = "g_check_incomplete"
        repair_class = "target_goal_break"
        need_hint = (
            "H holds on the completed scan, but no G-breaking assignment was found before "
            "the G scan cap. Change the family toward a concrete goal-breaking witness."
        )

    state = protocol_state(
        "FalseModelFamilyState",
        status,
        "false_model_family",
        tool="false_model_family",
        family_summary=family_summary,
        h_profile=h_profile,
        g_profile=g_profile,
        repair_class=repair_class,
        elapsed_seconds=round(time.monotonic() - started, 4),
        trust_boundary="The LLM family is untrusted; only complete universal H validation plus a concrete G failure can produce a certificate.",
        need_hint=need_hint,
    )
    return ((len(table), table) if status == "found" else None), state


def local_search_route(h_eq: dict[str, Any], g_eq: dict[str, Any], n: int, seed: int, budget: float):
    rng = random.Random(seed)
    deadline = time.monotonic() + budget
    h_assignments = list(product(range(n), repeat=len(h_eq["variables"])))
    while time.monotonic() < deadline:
        table = [[rng.randrange(n) for _ in range(n)] for _ in range(n)]
        for _ in range(3000):
            if time.monotonic() >= deadline:
                break
            violated: list[list[tuple[int, int]]] = []
            for vals in h_assignments:
                env = dict(zip(h_eq["variables"], vals))
                touched: list[tuple[int, int]] = []
                if trace_eval(h_eq["lhs"], env, table, touched) != trace_eval(h_eq["rhs"], env, table, touched):
                    violated.append(touched)
            if not violated:
                if is_counterexample(h_eq, g_eq, table):
                    return table
                break
            cells = list(set(rng.choice(violated))) or [(rng.randrange(n), rng.randrange(n))]
            if rng.random() < 0.35:
                a, b = rng.choice(cells)
                table[a][b] = rng.randrange(n)
                continue
            best = None
            sample = cells[:]
            rng.shuffle(sample)
            for a, b in sample[:6]:
                old = table[a][b]
                for val in range(n):
                    if val == old:
                        continue
                    table[a][b] = val
                    count = 0
                    for vals in h_assignments:
                        env = dict(zip(h_eq["variables"], vals))
                        if eval_term(h_eq["lhs"], env, table) != eval_term(h_eq["rhs"], env, table):
                            count += 1
                    if best is None or count < best[0]:
                        best = (count, a, b, val)
                table[a][b] = old
            if best is not None:
                _, a, b, val = best
                table[a][b] = val
    return None


def mf_eval(term: Term, env: dict[str, int], table: list[list[int | None]]) -> tuple[int | None, tuple[int, int] | None]:
    if term[0] == "var":
        return env[term[1]], None
    left, left_block = mf_eval(term[1], env, table)
    if left_block is not None:
        return None, left_block
    right, right_block = mf_eval(term[2], env, table)
    if right_block is not None:
        return None, right_block
    value = table[left][right]  # type: ignore[index]
    if value is None:
        return None, (left, right)  # type: ignore[arg-type]
    return value, None


def mf_force_top(side: Term, env: dict[str, int], table: list[list[int | None]], val: int) -> bool:
    if side[0] != "op":
        return False
    left, left_block = mf_eval(side[1], env, table)
    if left_block is not None:
        return False
    right, right_block = mf_eval(side[2], env, table)
    if right_block is not None:
        return False
    if table[left][right] is None:  # type: ignore[index]
        table[left][right] = val  # type: ignore[index]
        return True
    return False


def mf_propagate(
    table: list[list[int | None]],
    envs: list[dict[str, int]],
    lhs: Term,
    rhs: Term,
    stats: dict[str, Any] | None = None,
) -> bool:
    changed = True
    while changed:
        changed = False
        for env in envs:
            av, ab = mf_eval(lhs, env, table)
            bv, bb = mf_eval(rhs, env, table)
            if stats is not None:
                stats["propagation_checks"] = stats.get("propagation_checks", 0) + 1
                for block in (ab, bb):
                    if block is not None:
                        stats.setdefault("blocked_cells", Counter())[block] += 1
            if ab is None and bb is None:
                if av != bv:
                    if stats is not None:
                        stats["contradictions"] = stats.get("contradictions", 0) + 1
                    return False
            elif ab is None and av is not None:
                if mf_force_top(rhs, env, table, av):
                    if stats is not None:
                        stats["forced_assignments"] = stats.get("forced_assignments", 0) + 1
                    changed = True
            elif bb is None and bv is not None:
                if mf_force_top(lhs, env, table, bv):
                    if stats is not None:
                        stats["forced_assignments"] = stats.get("forced_assignments", 0) + 1
                    changed = True
    return True


def partial_table_profile(table: list[list[int | None]]) -> dict[str, Any]:
    n = len(table)
    assigned = sum(1 for row in table for x in row if x is not None)
    rows = []
    for i, row in enumerate(table):
        values = [x for x in row if x is not None]
        rows.append({
            "row": i,
            "assigned": len(values),
            "unique_values": len(set(values)),
        })
    return {
        "size": n,
        "assigned_cells": assigned,
        "unknown_cells": n * n - assigned,
        "row_profiles": rows,
    }


def top_counter(counter: Counter, limit: int = 8) -> list[dict[str, Any]]:
    return [
        {"cell": [int(cell[0]), int(cell[1])], "count": int(count)}
        for cell, count in counter.most_common(limit)
    ]


def propagation_model_finder(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    n: int,
    time_budget: float = 8.0,
    node_cap: int = 1_000_000,
) -> tuple[str, list[list[int]] | None, dict[str, Any]]:
    envs_h = [dict(zip(h_eq["variables"], vals)) for vals in product(range(n), repeat=len(h_eq["variables"]))]
    envs_g = [dict(zip(g_eq["variables"], vals)) for vals in product(range(n), repeat=len(g_eq["variables"]))]
    deadline = time.monotonic() + time_budget
    nodes = 0
    status = "none"
    stats: dict[str, Any] = {
        "forced_assignments": 0,
        "contradictions": 0,
        "propagation_checks": 0,
        "blocked_cells": Counter(),
        "branch_cells": Counter(),
    }
    best_partial: dict[str, Any] | None = None
    best_assigned = -1

    def violates_goal(table: list[list[int | None]]) -> bool:
        for env in envs_g:
            av, ab = mf_eval(g_eq["lhs"], env, table)
            bv, bb = mf_eval(g_eq["rhs"], env, table)
            if ab is None and bb is None and av != bv:
                return True
        return False

    def pick_cell(table: list[list[int | None]]) -> tuple[int, int] | None:
        for env in envs_h:
            for side in (h_eq["lhs"], h_eq["rhs"]):
                _, block = mf_eval(side, env, table)
                if block is not None and table[block[0]][block[1]] is None:
                    return block
        for i in range(n):
            for j in range(n):
                if table[i][j] is None:
                    return (i, j)
        return None

    def search(table: list[list[int | None]]) -> list[list[int | None]] | None:
        nonlocal nodes, status, best_partial, best_assigned
        if time.monotonic() > deadline or nodes > node_cap:
            status = "budget"
            return None
        nodes += 1
        trial = [row[:] for row in table]
        if not mf_propagate(trial, envs_h, h_eq["lhs"], h_eq["rhs"], stats):
            return None
        assigned = sum(1 for row in trial for x in row if x is not None)
        if assigned > best_assigned:
            best_assigned = assigned
            best_partial = partial_table_profile(trial)
        cell = pick_cell(trial)
        if cell is None:
            return trial if violates_goal(trial) else None
        i, j = cell
        stats["branch_cells"][(i, j)] += 1
        for value in range(n):
            trial[i][j] = value
            found = search(trial)
            if found is not None:
                return found
            if status == "budget":
                return None
            trial[i][j] = None
        return None

    found = search([[None] * n for _ in range(n)])
    meta = {
        "nodes": nodes,
        "n": n,
        "time_budget": time_budget,
        "node_cap": node_cap,
        "forced_assignments": stats["forced_assignments"],
        "contradictions": stats["contradictions"],
        "propagation_checks": stats["propagation_checks"],
        "top_blocked_cells": top_counter(stats["blocked_cells"]),
        "top_branch_cells": top_counter(stats["branch_cells"]),
        "best_partial_table_profile": best_partial,
    }
    if found is not None:
        return "found", [[int(x) for x in row] for row in found], meta
    return status, None, meta


def canonical_skolem_assignments(k: int, n: int) -> list[tuple[int, ...]]:
    """Canonical assignments of k goal variables, up to relabeling."""
    out: list[tuple[int, ...]] = []

    def go(prefix: list[int], max_seen: int) -> None:
        if len(prefix) == k:
            out.append(tuple(prefix))
            return
        for value in range(min(max_seen + 1, n - 1) + 1):
            go(prefix + [value], max(max_seen, value))

    go([], -1)
    return out


def noncollapsed_skolem_order(skolems: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    """Try witness patterns with more separated goal variables first."""
    return [
        skolem
        for _, skolem in sorted(enumerate(skolems), key=lambda item: (-len(set(item[1])), item[0]))
    ]


def goal_directed_model_finder(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    n: int,
    time_budget: float = 8.0,
    node_cap: int = 3_000_000,
    seed: int = 0xC0FFEE,
) -> tuple[str, list[list[int]] | None, dict[str, Any]]:
    """Goal-directed finite-model search with native structured telemetry.

    Instead of finding any H-model and hoping it violates G, fix a canonical
    Skolem assignment where G is required to fail. Propagation can then prune
    branches where G is already forced true at that point.
    """
    envs_h = [dict(zip(h_eq["variables"], vals)) for vals in product(range(n), repeat=len(h_eq["variables"]))]
    gvars = g_eq["variables"]
    skolems = canonical_skolem_assignments(len(gvars), n) if gvars else [()]
    deadline = time.monotonic() + time_budget
    rng = random.Random(seed)
    trials: list[dict[str, Any]] = []
    totals = {
        "nodes": 0,
        "goal_prunes": 0,
        "time_cuts": 0,
        "cap_cuts": 0,
        "forced_assignments": 0,
        "contradictions": 0,
        "propagation_checks": 0,
        "blocked_cells": Counter(),
        "branch_cells": Counter(),
    }
    best_partial: dict[str, Any] | None = None
    best_assigned = -1
    final_status = "none"

    def pick_cell(table: list[list[int | None]], sviol: dict[str, int]) -> tuple[int, int] | None:
        for side in (g_eq["lhs"], g_eq["rhs"]):
            _, block = mf_eval(side, sviol, table)
            if block is not None and table[block[0]][block[1]] is None:
                return block
        for env in envs_h:
            for side in (h_eq["lhs"], h_eq["rhs"]):
                _, block = mf_eval(side, env, table)
                if block is not None and table[block[0]][block[1]] is None:
                    return block
        for i in range(n):
            for j in range(n):
                if table[i][j] is None:
                    return (i, j)
        return None

    def one_pass(sviol: dict[str, int], cap: int, sub_deadline: float) -> tuple[str, list[list[int | None]] | None, dict[str, Any]]:
        nonlocal best_partial, best_assigned
        local_nodes = 0
        local_goal_prunes = 0
        outcome = "none"
        base = max(sviol.values()) if sviol else -1

        def search(table: list[list[int | None]]) -> list[list[int | None]] | None:
            nonlocal local_nodes, local_goal_prunes, outcome, best_partial, best_assigned
            if time.monotonic() > sub_deadline:
                outcome = "time"
                return None
            if local_nodes > cap:
                outcome = "cap"
                return None
            local_nodes += 1
            totals["nodes"] += 1
            trial = [row[:] for row in table]
            if not mf_propagate(trial, envs_h, h_eq["lhs"], h_eq["rhs"], totals):
                return None
            assigned = sum(1 for row in trial for x in row if x is not None)
            if assigned > best_assigned:
                best_assigned = assigned
                best_partial = partial_table_profile(trial)
            glv, glb = mf_eval(g_eq["lhs"], sviol, trial)
            grv, grb = mf_eval(g_eq["rhs"], sviol, trial)
            if glb is None and grb is None and glv == grv:
                local_goal_prunes += 1
                totals["goal_prunes"] += 1
                return None
            cell = pick_cell(trial, sviol)
            if cell is None:
                return trial
            i, j = cell
            totals["branch_cells"][(i, j)] += 1
            max_value = base
            for row in trial:
                for value in row:
                    if value is not None and value > max_value:
                        max_value = value
            hi = max_value + 1 if max_value + 1 < n else n - 1
            candidates = list(range(hi + 1))
            rng.shuffle(candidates)
            for value in candidates:
                trial[i][j] = value
                found = search(trial)
                if found is not None:
                    return found
                if outcome in {"cap", "time"}:
                    return None
                trial[i][j] = None
            return None

        found = search([[None] * n for _ in range(n)])
        meta = {
            "skolem": dict(sviol),
            "cap": cap,
            "nodes": local_nodes,
            "goal_prunes": local_goal_prunes,
            "outcome": "found" if found is not None else outcome,
        }
        if found is not None:
            return "found", found, meta
        if outcome == "time":
            totals["time_cuts"] += 1
        elif outcome == "cap":
            totals["cap_cuts"] += 1
        return outcome, None, meta

    for idx, skolem_tuple in enumerate(skolems):
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            final_status = "budget"
            break
        sviol = dict(zip(gvars, skolem_tuple))
        sub_deadline = time.monotonic() + remaining / max(1, len(skolems) - idx)
        cap = 30_000
        resolved = False
        while time.monotonic() < sub_deadline:
            status, table, meta = one_pass(sviol, cap, sub_deadline)
            trials.append(meta)
            if status == "found" and table is not None:
                complete = [[int(x) for x in row] for row in table]
                return "found", complete, {
                    "n": n,
                    "time_budget": time_budget,
                    "node_cap": node_cap,
                    "skolem_count": len(skolems),
                    "trials": trials[-8:],
                    "nodes": totals["nodes"],
                    "goal_prunes": totals["goal_prunes"],
                    "forced_assignments": totals["forced_assignments"],
                    "contradictions": totals["contradictions"],
                    "propagation_checks": totals["propagation_checks"],
                    "top_blocked_cells": top_counter(totals["blocked_cells"]),
                    "top_branch_cells": top_counter(totals["branch_cells"]),
                    "best_partial_table_profile": best_partial,
                }
            if status == "none":
                resolved = True
                break
            if status == "time":
                break
            cap = min(cap * 2, node_cap)
        if not resolved:
            final_status = "budget"
    return final_status, None, {
        "n": n,
        "time_budget": time_budget,
        "node_cap": node_cap,
        "skolem_count": len(skolems),
        "trials": trials[-8:],
        "nodes": totals["nodes"],
        "goal_prunes": totals["goal_prunes"],
        "time_cuts": totals["time_cuts"],
        "cap_cuts": totals["cap_cuts"],
        "forced_assignments": totals["forced_assignments"],
        "contradictions": totals["contradictions"],
        "propagation_checks": totals["propagation_checks"],
        "top_blocked_cells": top_counter(totals["blocked_cells"]),
        "top_branch_cells": top_counter(totals["branch_cells"]),
        "best_partial_table_profile": best_partial,
    }


_CP_SAT_AVAILABLE: bool | None = None


def cp_sat_available() -> bool:
    global _CP_SAT_AVAILABLE
    if _CP_SAT_AVAILABLE is not None:
        return _CP_SAT_AVAILABLE
    try:
        from ortools.sat.python import cp_model  # noqa: F401

        _CP_SAT_AVAILABLE = True
    except Exception:
        _CP_SAT_AVAILABLE = False
    return _CP_SAT_AVAILABLE


def cp_sat_counterexample_search(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    n: int,
    time_budget: float = 8.0,
    workers: int = 8,
) -> tuple[str, list[list[int]] | None, dict[str, Any]]:
    """Optional exact finite-model route using OR-Tools when available.

    This is deliberately wrapped as a false_model_search route. Environments
    without OR-Tools simply return `unavailable`, preserving the single-file
    submission behavior while letting richer local environments exercise a
    stronger finite-domain consumer.
    """
    if not cp_sat_available():
        return "unavailable", None, {
            "n": n,
            "reason": "ortools.sat.python.cp_model is not available",
        }
    from ortools.sat.python import cp_model

    gvars = g_eq["variables"]
    skolems = canonical_skolem_assignments(len(gvars), n) if gvars else [()]
    deadline = time.monotonic() + max(0.2, time_budget)
    trials: list[dict[str, Any]] = []

    def build_and_solve(skolem: tuple[int, ...], sub_budget: float) -> tuple[str, list[list[int]] | None, dict[str, Any]]:
        model = cp_model.CpModel()
        op = {
            (i, j): model.NewIntVar(0, n - 1, f"op_{i}_{j}")
            for i in range(n)
            for j in range(n)
        }
        flat = [op[(i, j)] for i in range(n) for j in range(n)]
        aux_id = 0

        def cp_eval(term: Term, env: dict[str, int]) -> Any:
            nonlocal aux_id
            if term[0] == "var":
                return env[term[1]]
            left = cp_eval(term[1], env)
            right = cp_eval(term[2], env)
            if isinstance(left, int) and isinstance(right, int):
                return op[(left, right)]
            idx = model.NewIntVar(0, n * n - 1, f"idx_{aux_id}")
            out = model.NewIntVar(0, n - 1, f"val_{aux_id}")
            aux_id += 1
            model.Add(idx == left * n + right)
            model.AddElement(idx, flat, out)
            return out

        for vals in product(range(n), repeat=len(h_eq["variables"])):
            env = dict(zip(h_eq["variables"], vals))
            model.Add(cp_eval(h_eq["lhs"], env) == cp_eval(h_eq["rhs"], env))

        goal_env = dict(zip(gvars, skolem))
        model.Add(cp_eval(g_eq["lhs"], goal_env) != cp_eval(g_eq["rhs"], goal_env))

        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = max(0.1, sub_budget)
        solver.parameters.num_search_workers = max(1, min(int(workers), 16))
        status = solver.Solve(model)
        name = solver.StatusName(status)
        meta = {
            "skolem": dict(goal_env),
            "status": name,
            "wall_time": round(float(solver.WallTime()), 3),
            "branches": int(solver.NumBranches()),
            "conflicts": int(solver.NumConflicts()),
            "aux_terms": aux_id,
        }
        if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            table = [[int(solver.Value(op[(i, j)])) for j in range(n)] for i in range(n)]
            return "found", table, meta
        if status == cp_model.INFEASIBLE:
            return "infeasible", None, meta
        return "unknown", None, meta

    final_status = "none"
    for idx, skolem in enumerate(skolems):
        remaining = deadline - time.monotonic()
        if remaining <= 0.05:
            final_status = "budget"
            break
        sub_budget = remaining / max(1, len(skolems) - idx)
        status, table, meta = build_and_solve(skolem, sub_budget)
        trials.append(meta)
        if status == "found" and table is not None:
            return "found", table, {
                "n": n,
                "time_budget": time_budget,
                "skolem_count": len(skolems),
                "trials": trials,
            }
        if status in {"unknown", "budget"}:
            final_status = "budget"
        elif final_status == "none":
            final_status = "infeasible"
    return final_status, None, {
        "n": n,
        "time_budget": time_budget,
        "skolem_count": len(skolems),
        "trials": trials,
        "cp_sat_infeasible_skolems": sum(1 for t in trials if t.get("status") == "INFEASIBLE"),
        "cp_sat_unknown_skolems": sum(1 for t in trials if t.get("status") not in {"INFEASIBLE", "OPTIMAL", "FEASIBLE"}),
    }


def affine_skew_fiber_library(size: int) -> list[dict[str, Any]]:
    """Compact binary maps used inside quotient-by-fiber countermodels."""
    rows: list[dict[str, Any]] = []
    seen: set[tuple[int, ...]] = set()
    for a, b, c in product(range(size), repeat=3):
        table = tuple(
            (a * left + b * right + c) % size
            for left in range(size)
            for right in range(size)
        )
        if table in seen:
            continue
        seen.add(table)
        rows.append({"params": [a, b, c], "table": table})
    return rows


def skew_cp_eval(
    model: Any,
    term: Term,
    env: dict[str, Any],
    flat_operation: list[Any],
    carrier_size: int,
    counter: list[int],
    prefix: str,
) -> Any:
    if term[0] == "var":
        return env[term[1]]
    left = skew_cp_eval(
        model, term[1], env, flat_operation, carrier_size, counter, prefix
    )
    right = skew_cp_eval(
        model, term[2], env, flat_operation, carrier_size, counter, prefix
    )
    if isinstance(left, int) and isinstance(right, int):
        return flat_operation[left * carrier_size + right]
    index = model.NewIntVar(
        0,
        carrier_size * carrier_size - 1,
        f"{prefix}_index_{counter[0]}",
    )
    value = model.NewIntVar(
        0,
        carrier_size - 1,
        f"{prefix}_value_{counter[0]}",
    )
    counter[0] += 1
    model.Add(index == left * carrier_size + right)
    model.AddElement(index, flat_operation, value)
    return value


def skew_equation_failure(
    equation: dict[str, Any],
    table: list[list[int]],
    deadline: float,
) -> dict[str, int] | None:
    for values in product(
        range(len(table)), repeat=len(equation["variables"])
    ):
        if time.monotonic() >= deadline:
            raise TimeoutError
        env = dict(zip(equation["variables"], values))
        if (
            eval_term(equation["lhs"], env, table)
            != eval_term(equation["rhs"], env, table)
        ):
            return {key: int(value) for key, value in env.items()}
    return None


def pure_python_skew_product_search(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    control_size: int,
    fiber_size: int,
    time_budget: float,
    *,
    require_quotient_goal: bool,
) -> tuple[str, list[list[int]] | None, dict[str, Any]]:
    """Dependency-free compact search for the official solver sandbox."""
    started = time.monotonic()
    deadline = started + max(0.5, float(time_budget))
    carrier_size = control_size * fiber_size
    library = affine_skew_fiber_library(fiber_size)

    # Low-description-complexity maps first: projections and shifted
    # projections precede genuinely binary affine maps. This is a semantic
    # search order over the family, not a problem-specific selector tuple.
    selector_order = sorted(
        range(len(library)),
        key=lambda index: (
            (
                0
                if library[index]["params"][:2] == [1, 0]
                else 1
                if library[index]["params"][:2] == [0, 1]
                else 2
                if (
                    library[index]["params"][0] != 0
                    and library[index]["params"][1] == 0
                )
                else 3
                if library[index]["params"][:2] == [0, 0]
                else 4
                if library[index]["params"][0] == 0
                else 5
            ),
            library[index]["params"][2],
            library[index]["params"][0],
            library[index]["params"][1],
        ),
    )
    quotient_tables_checked = 0
    quotient_candidates = 0
    selector_tuples_checked = 0

    try:
        for flat_control in product(
            range(control_size),
            repeat=control_size * control_size,
        ):
            if time.monotonic() >= deadline:
                raise TimeoutError
            quotient_tables_checked += 1
            control_table = [
                list(
                    flat_control[
                        row * control_size : (row + 1) * control_size
                    ]
                )
                for row in range(control_size)
            ]
            if skew_equation_failure(h_eq, control_table, deadline) is not None:
                continue
            if (
                require_quotient_goal
                and skew_equation_failure(
                    g_eq, control_table, deadline
                )
                is not None
            ):
                continue
            quotient_candidates += 1

            for selectors in product(
                selector_order,
                repeat=control_size * control_size,
            ):
                selector_tuples_checked += 1
                if (
                    (selector_tuples_checked & 255) == 0
                    and time.monotonic() >= deadline
                ):
                    raise TimeoutError
                table: list[list[int]] = []
                for left in range(carrier_size):
                    left_control, left_fiber = divmod(left, fiber_size)
                    row = []
                    for right in range(carrier_size):
                        right_control, right_fiber = divmod(right, fiber_size)
                        selector = selectors[
                            left_control * control_size + right_control
                        ]
                        fiber_value = library[selector]["table"][
                            left_fiber * fiber_size + right_fiber
                        ]
                        row.append(
                            control_table[left_control][right_control]
                            * fiber_size
                            + int(fiber_value)
                        )
                    table.append(row)

                goal_witness = skew_equation_failure(g_eq, table, deadline)
                if goal_witness is None:
                    continue
                if skew_equation_failure(h_eq, table, deadline) is not None:
                    continue
                return "found", table, {
                    "template": "skew_product",
                    "status": "verified_countermodel",
                    "backend": "pure_python_enumeration",
                    "control_size": control_size,
                    "fiber_size": fiber_size,
                    "carrier_size": carrier_size,
                    "quotient_tables_checked": quotient_tables_checked,
                    "quotient_candidates": quotient_candidates,
                    "selector_tuples_checked": selector_tuples_checked,
                    "control_table": control_table,
                    "fiber_parameters": {
                        f"{left},{right}": list(
                            library[
                                selectors[left * control_size + right]
                            ]["params"]
                        )
                        for left in range(control_size)
                        for right in range(control_size)
                    },
                    "goal_witness": goal_witness,
                    "seconds": round(time.monotonic() - started, 3),
                }
    except TimeoutError:
        return "budget", None, {
            "template": "skew_product",
            "status": "search_incomplete",
            "backend": "pure_python_enumeration",
            "control_size": control_size,
            "fiber_size": fiber_size,
            "carrier_size": carrier_size,
            "quotient_tables_checked": quotient_tables_checked,
            "quotient_candidates": quotient_candidates,
            "selector_tuples_checked": selector_tuples_checked,
            "seconds": round(time.monotonic() - started, 3),
            "suggested_factorizations": [
                [fiber_size, control_size],
                [control_size, min(8, fiber_size + 1)],
            ],
        }
    return "infeasible", None, {
        "template": "skew_product",
        "status": "family_infeasible",
        "backend": "pure_python_enumeration",
        "control_size": control_size,
        "fiber_size": fiber_size,
        "carrier_size": carrier_size,
        "quotient_tables_checked": quotient_tables_checked,
        "quotient_candidates": quotient_candidates,
        "selector_tuples_checked": selector_tuples_checked,
        "seconds": round(time.monotonic() - started, 3),
        "suggested_factorizations": [
            [fiber_size, control_size],
            [control_size, min(8, fiber_size + 1)],
        ],
    }


def skew_product_counterexample_search(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    control_size: int = 2,
    fiber_size: int = 3,
    time_budget: float = 4.0,
    *,
    require_quotient_goal: bool = True,
    max_iterations: int = 64,
    violation_batch: int = 12,
    workers: int = 8,
    seed: int = 0,
) -> tuple[str, list[list[int]] | None, dict[str, Any]]:
    """Synthesize a compact quotient-by-fiber model.

    Each element is `(q, f)`. The quotient operation is synthesized, while
    every quotient cell selects one affine binary map on the fiber. Requiring
    the quotient to satisfy both H and G means a found counterexample is
    created by the extension rather than inherited from a smaller table.
    The approved sandbox uses dependency-free enumeration; optional CP-SAT
    accelerates the same family with CEGIS when available.
    """
    control_size = max(1, min(6, int(control_size)))
    fiber_size = max(2, min(8, int(fiber_size)))
    carrier_size = control_size * fiber_size
    if carrier_size > 40:
        return "invalid_factorization", None, {
            "template": "skew_product",
            "control_size": control_size,
            "fiber_size": fiber_size,
            "carrier_size": carrier_size,
            "reason": "compact skew search is limited to 40 elements",
        }
    if not cp_sat_available():
        return pure_python_skew_product_search(
            h_eq,
            g_eq,
            control_size,
            fiber_size,
            time_budget,
            require_quotient_goal=require_quotient_goal,
        )

    from ortools.sat.python import cp_model

    started = time.monotonic()
    deadline = started + max(0.5, float(time_budget))
    library = affine_skew_fiber_library(fiber_size)
    model = cp_model.CpModel()
    control = {
        (left, right): model.NewIntVar(
            0, control_size - 1, f"skew_control_{left}_{right}"
        )
        for left in range(control_size)
        for right in range(control_size)
    }
    selectors = {
        (left, right): model.NewIntVar(
            0, len(library) - 1, f"skew_selector_{left}_{right}"
        )
        for left in range(control_size)
        for right in range(control_size)
    }
    operation = {
        (left, right): model.NewIntVar(
            0, carrier_size - 1, f"skew_operation_{left}_{right}"
        )
        for left in range(carrier_size)
        for right in range(carrier_size)
    }
    flat_control = [
        control[(left, right)]
        for left in range(control_size)
        for right in range(control_size)
    ]
    flat_operation = [
        operation[(left, right)]
        for left in range(carrier_size)
        for right in range(carrier_size)
    ]

    for left in range(carrier_size):
        left_control, left_fiber = divmod(left, fiber_size)
        for right in range(carrier_size):
            right_control, right_fiber = divmod(right, fiber_size)
            fiber_value = model.NewIntVar(
                0, fiber_size - 1, f"skew_fiber_value_{left}_{right}"
            )
            outputs = [
                int(row["table"][left_fiber * fiber_size + right_fiber])
                for row in library
            ]
            model.AddElement(
                selectors[(left_control, right_control)],
                outputs,
                fiber_value,
            )
            model.Add(
                operation[(left, right)]
                == control[(left_control, right_control)] * fiber_size
                + fiber_value
            )

    quotient_aux = [0]
    quotient_obligations = 0

    def add_quotient_equation(equation: dict[str, Any], label: str) -> None:
        nonlocal quotient_obligations
        for values in product(
            range(control_size), repeat=len(equation["variables"])
        ):
            env = dict(zip(equation["variables"], values))
            left = skew_cp_eval(
                model,
                equation["lhs"],
                env,
                flat_control,
                control_size,
                quotient_aux,
                f"skew_quotient_{label}",
            )
            right = skew_cp_eval(
                model,
                equation["rhs"],
                env,
                flat_control,
                control_size,
                quotient_aux,
                f"skew_quotient_{label}",
            )
            model.Add(left == right)
            quotient_obligations += 1

    add_quotient_equation(h_eq, "h")
    if require_quotient_goal:
        add_quotient_equation(g_eq, "g")

    goal_aux = [0]
    goal_env = {
        variable: model.NewIntVar(
            0, carrier_size - 1, f"skew_goal_witness_{variable}"
        )
        for variable in g_eq["variables"]
    }
    goal_left = skew_cp_eval(
        model,
        g_eq["lhs"],
        goal_env,
        flat_operation,
        carrier_size,
        goal_aux,
        "skew_goal",
    )
    goal_right = skew_cp_eval(
        model,
        g_eq["rhs"],
        goal_env,
        flat_operation,
        carrier_size,
        goal_aux,
        "skew_goal",
    )
    model.Add(goal_left != goal_right)

    h_constraints: set[tuple[int, ...]] = set()
    lifted_aux = [0]

    def add_h_assignment(values: tuple[int, ...]) -> None:
        if values in h_constraints:
            return
        h_constraints.add(values)
        env = dict(zip(h_eq["variables"], values))
        left = skew_cp_eval(
            model,
            h_eq["lhs"],
            env,
            flat_operation,
            carrier_size,
            lifted_aux,
            "skew_lifted_h",
        )
        right = skew_cp_eval(
            model,
            h_eq["rhs"],
            env,
            flat_operation,
            carrier_size,
            lifted_aux,
            "skew_lifted_h",
        )
        model.Add(left == right)

    for values in product(
        range(control_size), repeat=len(h_eq["variables"])
    ):
        add_h_assignment(tuple(value * fiber_size for value in values))
    for value in range(carrier_size):
        add_h_assignment(tuple(value for _ in h_eq["variables"]))

    events: list[dict[str, Any]] = []
    assignments_checked = 0
    for iteration in range(1, max(1, min(int(max_iterations), 500)) + 1):
        remaining = deadline - time.monotonic()
        if remaining <= 0.05:
            break
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = max(0.05, remaining)
        solver.parameters.num_search_workers = max(1, min(int(workers), 16))
        solver.parameters.random_seed = int(seed) + iteration - 1
        cp_status = solver.Solve(model)
        event: dict[str, Any] = {
            "iteration": iteration,
            "cp_status": solver.StatusName(cp_status),
            "wall_time": round(float(solver.WallTime()), 3),
            "branches": int(solver.NumBranches()),
            "conflicts": int(solver.NumConflicts()),
            "lifted_h_constraints": len(h_constraints),
        }
        events.append(event)
        if cp_status == cp_model.INFEASIBLE:
            return "infeasible", None, {
                "template": "skew_product",
                "status": "family_infeasible",
                "backend": "ortools_cp_sat_cegis",
                "control_size": control_size,
                "fiber_size": fiber_size,
                "carrier_size": carrier_size,
                "quotient_obligations": quotient_obligations,
                "lifted_h_constraints": len(h_constraints),
                "iterations": iteration,
                "events": events[-6:],
                "suggested_factorizations": [
                    [fiber_size, control_size],
                    [control_size, min(8, fiber_size + 1)],
                ],
            }
        if cp_status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            break

        table = [
            [
                int(solver.Value(operation[(left, right)]))
                for right in range(carrier_size)
            ]
            for left in range(carrier_size)
        ]
        witness_env = {
            variable: int(solver.Value(value))
            for variable, value in goal_env.items()
        }
        violations: list[tuple[int, ...]] = []
        scan_complete = True
        checked = 0
        for values in product(
            range(carrier_size), repeat=len(h_eq["variables"])
        ):
            if time.monotonic() >= deadline:
                scan_complete = False
                break
            checked += 1
            env = dict(zip(h_eq["variables"], values))
            if (
                eval_term(h_eq["lhs"], env, table)
                == eval_term(h_eq["rhs"], env, table)
            ):
                continue
            violations.append(tuple(int(value) for value in values))
            if len(violations) >= max(1, min(int(violation_batch), 64)):
                scan_complete = False
                break
        assignments_checked += checked
        event.update({
            "h_assignments_checked": checked,
            "h_scan_complete": scan_complete,
            "h_violations_found": len(violations),
            "goal_witness": {
                "env": witness_env,
                "lhs": eval_term(g_eq["lhs"], witness_env, table),
                "rhs": eval_term(g_eq["rhs"], witness_env, table),
            },
        })
        if scan_complete and not violations:
            if not is_counterexample(h_eq, g_eq, table):
                return "internal_error", None, {
                    "template": "skew_product",
                    "status": "verification_mismatch",
                    "backend": "ortools_cp_sat_cegis",
                    "events": events[-6:],
                }
            selectors_out = {
                f"{left},{right}": list(
                    library[int(solver.Value(selectors[(left, right)]))]["params"]
                )
                for left in range(control_size)
                for right in range(control_size)
            }
            control_table = [
                [
                    int(solver.Value(control[(left, right)]))
                    for right in range(control_size)
                ]
                for left in range(control_size)
            ]
            return "found", table, {
                "template": "skew_product",
                "status": "verified_countermodel",
                "backend": "ortools_cp_sat_cegis",
                "control_size": control_size,
                "fiber_size": fiber_size,
                "carrier_size": carrier_size,
                "quotient_obligations": quotient_obligations,
                "lifted_h_constraints": len(h_constraints),
                "iterations": iteration,
                "h_assignments_checked_total": assignments_checked,
                "control_table": control_table,
                "fiber_parameters": selectors_out,
                "goal_witness": event["goal_witness"],
                "events": events[-6:],
                "seconds": round(time.monotonic() - started, 3),
            }
        if not violations:
            break
        for values in violations:
            add_h_assignment(values)

    return "budget", None, {
        "template": "skew_product",
        "status": "search_incomplete",
        "backend": "ortools_cp_sat_cegis",
        "control_size": control_size,
        "fiber_size": fiber_size,
        "carrier_size": carrier_size,
        "quotient_obligations": quotient_obligations,
        "lifted_h_constraints": len(h_constraints),
        "iterations": len(events),
        "h_assignments_checked_total": assignments_checked,
        "events": events[-6:],
        "seconds": round(time.monotonic() - started, 3),
        "suggested_factorizations": [
            [fiber_size, control_size],
            [control_size, min(8, fiber_size + 1)],
        ],
    }


_SYMPY_SAT_AVAILABLE: bool | None = None


def sympy_sat_available() -> bool:
    global _SYMPY_SAT_AVAILABLE
    if _SYMPY_SAT_AVAILABLE is not None:
        return _SYMPY_SAT_AVAILABLE
    try:
        from sympy.logic.inference import satisfiable  # noqa: F401

        _SYMPY_SAT_AVAILABLE = True
    except Exception:
        _SYMPY_SAT_AVAILABLE = False
    return _SYMPY_SAT_AVAILABLE


class SympySatTimeout(Exception):
    pass


def sympy_sat_counterexample_search(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    n: int,
    time_budget: float = 120.0,
) -> tuple[str, list[list[int]] | None, dict[str, Any]]:
    """Exact finite-model route using sympy's pure-Python SAT engine.

    This is a competition-sandbox-friendly sibling of the optional OR-Tools
    route. It encodes one fixed carrier size and one canonical Skolem
    assignment at a time, requiring H everywhere and G to fail at that point.
    """
    if n < 5:
        return "skipped_small_size", None, {
            "n": n,
            "reason": "sympy_sat deliberately skips n < 5; tiny UNSAT searches are slow and not the target niche",
        }
    if not sympy_sat_available():
        return "unavailable", None, {
            "n": n,
            "reason": "sympy.logic.inference.satisfiable is not available",
        }

    from sympy import Symbol
    from sympy.logic.algorithms.dpll2 import EncodedCNF
    from sympy.logic.inference import satisfiable

    gvars = g_eq["variables"]
    skolems = noncollapsed_skolem_order(canonical_skolem_assignments(len(gvars), n)) if gvars else [()]
    envs_h = [dict(zip(h_eq["variables"], vals)) for vals in product(range(n), repeat=len(h_eq["variables"]))]
    true_lit: int | None = None
    false_lit = 0
    symbols: list[Any] = []
    clauses: list[set[int]] = []
    cell_vars: dict[tuple[int, int, int], int] = {}

    def new_var(name: str) -> int:
        symbols.append(Symbol(name))
        return len(symbols)

    for i in range(n):
        for j in range(n):
            vars_ij = [new_var(f"s_{n}_{i}_{j}_{k}") for k in range(n)]
            for k, var in enumerate(vars_ij):
                cell_vars[(i, j, k)] = var
            clauses.append(set(vars_ij))
            for a in range(n):
                for b in range(a + 1, n):
                    clauses.append({-vars_ij[a], -vars_ij[b]})

    def add_clause(lits: list[int | None]) -> None:
        if any(lit is true_lit for lit in lits):
            return
        reduced = {int(lit) for lit in lits if lit != false_lit}
        clauses.append(reduced if reduced else {false_lit})

    def add_unit(lit: int | None) -> None:
        add_clause([lit])

    def neg(lit: int | None) -> int | None:
        if lit is true_lit:
            return false_lit
        if lit == false_lit:
            return true_lit
        return -int(lit)

    def and_gate(inputs: list[int | None]) -> int | None:
        if any(lit == false_lit for lit in inputs):
            return false_lit
        active = [int(lit) for lit in inputs if lit is not true_lit]
        if not active:
            return true_lit
        if len(active) == 1:
            return active[0]
        out = new_var(f"a_{len(symbols) + 1}")
        for lit in active:
            add_clause([neg(out), lit])
        add_clause([out, *[neg(lit) for lit in active]])
        return out

    def or_gate(inputs: list[int | None]) -> int | None:
        if any(lit is true_lit for lit in inputs):
            return true_lit
        active = [int(lit) for lit in inputs if lit != false_lit]
        if not active:
            return false_lit
        if len(active) == 1:
            return active[0]
        out = new_var(f"o_{len(symbols) + 1}")
        for lit in active:
            add_clause([neg(lit), out])
        add_clause([neg(out), *active])
        return out

    def value_const(value: int) -> list[int | None]:
        return [true_lit if k == value else false_lit for k in range(n)]

    def eval_lits(term: Term, env: dict[str, int], memo: dict[Term, list[int | None]]) -> list[int | None]:
        if term in memo:
            return memo[term]
        if term[0] == "var":
            out = value_const(env[term[1]])
        else:
            left = eval_lits(term[1], env, memo)
            right = eval_lits(term[2], env, memo)
            out = []
            for k in range(n):
                disjuncts: list[int | None] = []
                for a in range(n):
                    for b in range(n):
                        disjuncts.append(and_gate([left[a], right[b], cell_vars[(a, b, k)]]))
                out.append(or_gate(disjuncts))
        memo[term] = out
        return out

    def require_equal(lhs: list[int | None], rhs: list[int | None]) -> None:
        for k in range(n):
            add_clause([neg(lhs[k]), rhs[k]])
            add_clause([lhs[k], neg(rhs[k])])

    def require_not_equal(lhs: list[int | None], rhs: list[int | None]) -> None:
        witnesses: list[int | None] = []
        for k in range(n):
            witnesses.append(and_gate([lhs[k], neg(rhs[k])]))
            witnesses.append(and_gate([rhs[k], neg(lhs[k])]))
        add_unit(or_gate(witnesses))

    # The route's whole cost — including this base-CNF construction, which
    # grows as n^|vars(H)| — must respect the caller's budget. Set the
    # deadline before grounding so a large H cannot stall past the window.
    deadline = time.monotonic() + max(0.5, time_budget)
    for env_idx, env in enumerate(envs_h):
        if env_idx % 8 == 0 and time.monotonic() >= deadline:
            return "timeout", None, {
                "n": n,
                "time_budget": time_budget,
                "phase": "encoding_h",
                "grounded_envs": env_idx,
                "env_count": len(envs_h),
            }
        memo_h: dict[Term, list[int | None]] = {}
        require_equal(eval_lits(h_eq["lhs"], env, memo_h), eval_lits(h_eq["rhs"], env, memo_h))

    base_clause_count = len(clauses)
    base_symbol_count = len(symbols)

    old_handler = signal.getsignal(signal.SIGALRM)
    old_timer = signal.getitimer(signal.ITIMER_REAL)

    def on_alarm(_signum: int, _frame: Any) -> None:
        raise SympySatTimeout()

    trials: list[dict[str, Any]] = []
    try:
        signal.signal(signal.SIGALRM, on_alarm)
        for idx, skolem in enumerate(skolems):
            remaining = deadline - time.monotonic()
            if remaining <= 0.25:
                return "timeout", None, {
                    "n": n,
                    "time_budget": time_budget,
                    "skolem_count": len(skolems),
                    "trials": trials,
                }
            if idx == 0 and len(skolems) > 1:
                sub_budget = min(remaining, max(0.2, remaining * 0.8))
            else:
                sub_budget = max(0.2, remaining / max(1, len(skolems) - idx))
            goal_env = dict(zip(gvars, skolem))
            signal.setitimer(signal.ITIMER_REAL, sub_budget)
            try:
                # The per-skolem goal encoding can rival the SAT call in cost,
                # so it must sit inside the protected window: an alarm firing
                # here previously escaped as an uncaught SympySatTimeout and
                # killed the entire solve.
                symbols = symbols[:base_symbol_count]
                clauses = [set(clause) for clause in clauses[:base_clause_count]]
                goal_memo: dict[Term, list[int | None]] = {}
                require_not_equal(eval_lits(g_eq["lhs"], goal_env, goal_memo), eval_lits(g_eq["rhs"], goal_env, goal_memo))
                enc = EncodedCNF([set(clause) for clause in clauses], {sym: i + 1 for i, sym in enumerate(symbols)})
                model = satisfiable(enc, algorithm="dpll2", all_models=False)
            except SympySatTimeout:
                trials.append({"skolem": dict(goal_env), "status": "timeout", "sub_budget": round(sub_budget, 3)})
                continue
            finally:
                signal.setitimer(signal.ITIMER_REAL, 0.0)
            if model is False:
                trials.append({"skolem": dict(goal_env), "status": "unsat", "sub_budget": round(sub_budget, 3)})
                continue
            table: list[list[int]] = []
            for i in range(n):
                row: list[int] = []
                for j in range(n):
                    chosen = [
                        k
                        for k in range(n)
                        if bool(model.get(symbols[cell_vars[(i, j, k)] - 1], False))
                    ]
                    row.append(int(chosen[0]) if chosen else 0)
                table.append(row)
            ok = is_counterexample(h_eq, g_eq, table)
            trials.append({
                "skolem": dict(goal_env),
                "status": "sat" if ok else "sat_but_local_check_failed",
                "sub_budget": round(sub_budget, 3),
            })
            if ok:
                return "found", table, {
                    "n": n,
                    "time_budget": time_budget,
                    "skolem_count": len(skolems),
                    "trials": trials,
                    "backend": "sympy.logic.inference.satisfiable",
                }
        return "unsat_or_timeout", None, {
            "n": n,
            "time_budget": time_budget,
            "skolem_count": len(skolems),
            "trials": trials,
            "backend": "sympy.logic.inference.satisfiable",
        }
    except SympySatTimeout:
        # Defense in depth: the per-skolem window above catches this, but if
        # the alarm ever fires outside a protected region, fail soft as a
        # clean timeout instead of killing the whole solve.
        return "timeout", None, {
            "n": n,
            "time_budget": time_budget,
            "skolem_count": len(skolems),
            "trials": trials,
        }
    finally:
        signal.setitimer(signal.ITIMER_REAL, old_timer[0], old_timer[1])
        signal.signal(signal.SIGALRM, old_handler)


PCE_AFFINE = [(0, 0), (1, 0), (0, 1)]
PCE_BILINEAR = [(0, 0), (1, 0), (0, 1), (1, 1)]
PCE_QUADRATIC = [(0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (0, 2)]
PCE_TIERS = [
    ("affine", PCE_AFFINE, 18),
    ("bilinear", PCE_BILINEAR, 13),
    ("quadratic", PCE_QUADRATIC, 10),
]


def polynomial_table(coeffs: tuple[int, ...], basis: list[tuple[int, int]], n: int) -> list[list[int]]:
    table = [[0] * n for _ in range(n)]
    for a in range(n):
        for b in range(n):
            total = 0
            for coeff, (ea, eb) in zip(coeffs, basis):
                if coeff:
                    total += coeff * (a ** ea) * (b ** eb)
            table[a][b] = total % n
    return table


def polynomial_formula(coeffs: tuple[int, ...], basis: list[tuple[int, int]], n: int) -> str:
    def mul(factors: list[str]) -> str:
        if not factors:
            return "1"
        expr = factors[0]
        for factor in factors[1:]:
            expr = f"Nat.mul ({expr}) {factor}"
        return expr

    terms: list[str] = []
    for coeff, (ea, eb) in zip(coeffs, basis):
        if coeff == 0:
            continue
        factors = ["i.val"] * ea + ["j.val"] * eb
        if coeff != 1 or not factors:
            factors.insert(0, str(coeff))
        terms.append(mul(factors))
    if not terms:
        total = "0"
    else:
        total = terms[0]
        for term in terms[1:]:
            total = f"Nat.add ({total}) ({term})"
    return f"Nat.mod ({total}) {n}"


def pce_eval(term: Term, env: dict[str, int], table: list[list[int]]) -> int:
    if term[0] == "var":
        return env[term[1]]
    return table[pce_eval(term[1], env, table)][pce_eval(term[2], env, table)]


def pce_holds(eq: dict[str, Any], n: int, table: list[list[int]], deadline: float, check_every: int = 4096) -> bool | None:
    for idx, vals in enumerate(product(range(n), repeat=len(eq["variables"]))):
        if idx % check_every == 0 and time.monotonic() > deadline:
            return None
        env = dict(zip(eq["variables"], vals))
        if pce_eval(eq["lhs"], env, table) != pce_eval(eq["rhs"], env, table):
            return False
    return True


def pce_fails(eq: dict[str, Any], n: int, table: list[list[int]], deadline: float, check_every: int = 4096) -> bool | None:
    for idx, vals in enumerate(product(range(n), repeat=len(eq["variables"]))):
        if idx % check_every == 0 and time.monotonic() > deadline:
            return None
        env = dict(zip(eq["variables"], vals))
        if pce_eval(eq["lhs"], env, table) != pce_eval(eq["rhs"], env, table):
            return True
    return False


def find_poly_counterexample(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    *,
    nmax: int = 18,
    time_budget: float = 12.0,
    max_tier: int | None = None,
) -> tuple[int, list[list[int]], str, dict[str, Any]] | None:
    deadline = time.monotonic() + time_budget
    tiers = PCE_TIERS if max_tier is None else PCE_TIERS[:max_tier]
    checked = 0
    tier_stats: list[dict[str, Any]] = []
    for tier_index, (tier_name, basis, tier_nmax) in enumerate(tiers, start=1):
        tier_checked = 0
        for n in range(2, min(nmax, tier_nmax) + 1):
            if time.monotonic() > deadline:
                tier_stats.append({"tier": tier_name, "checked": tier_checked, "status": "budget"})
                return None
            for coeffs in product(range(n), repeat=len(basis)):
                table = polynomial_table(tuple(int(c) for c in coeffs), basis, n)
                checked += 1
                tier_checked += 1
                h_ok = pce_holds(h_eq, n, table, deadline)
                if h_ok is None:
                    tier_stats.append({"tier": tier_name, "checked": tier_checked, "status": "budget"})
                    return None
                if not h_ok:
                    continue
                g_bad = pce_fails(g_eq, n, table, deadline)
                if g_bad is None:
                    tier_stats.append({"tier": tier_name, "checked": tier_checked, "status": "budget"})
                    return None
                if g_bad:
                    meta = {
                        "tier": tier_name,
                        "tier_index": tier_index,
                        "basis": basis,
                        "coefficients": list(coeffs),
                        "checked_candidates": checked,
                        "tier_stats": tier_stats + [{"tier": tier_name, "checked": tier_checked, "status": "found"}],
                    }
                    return n, table, polynomial_formula(tuple(int(c) for c in coeffs), basis, n), meta
        tier_stats.append({"tier": tier_name, "checked": tier_checked, "status": "exhausted"})
    return None


def false_route_continuations(trials: list[dict[str, Any]]) -> list[str]:
    tried = {str(t.get("route")) for t in trials if t.get("route") is not None}
    local_ns = sorted({int(t["n"]) for t in trials if "seed" in t and isinstance(t.get("n"), int)})
    model_ns = sorted({
        int(t["n"])
        for t in trials
        if "seed" not in t and t.get("template") != "cp_sat" and isinstance(t.get("n"), int)
    })
    cp_ns = sorted({int(t["n"]) for t in trials if t.get("template") == "cp_sat" and isinstance(t.get("n"), int)})
    skew_factors = [
        (int(t["control_size"]), int(t["fiber_size"]))
        for t in trials
        if t.get("template") == "skew_product"
        and isinstance(t.get("control_size"), int)
        and isinstance(t.get("fiber_size"), int)
    ]
    candidate_ns = unique(local_ns + [6] + [min(8, n + 1) for n in local_ns])
    out: list[str] = []

    def add(route: str) -> None:
        if route not in tried and route not in out:
            out.append(route)

    if cp_sat_available() and cp_ns:
        cp_next = [min(9, n + 1) for n in cp_ns[-2:]]
        base_ns = [5, 6] if max(cp_ns) <= 6 else []
        for n in unique(cp_next + base_ns):
            if 2 <= n <= 9:
                add(f"cp_sat:n={n}")
    if skew_factors:
        control, fiber = skew_factors[-1]
        for next_control, next_fiber in (
            (fiber, control),
            (control, min(8, fiber + 1)),
        ):
            if next_control * next_fiber <= 40:
                add(f"skew_product:{next_control}x{next_fiber}")
    else:
        add("skew_product:2x3")
    if sympy_sat_available():
        for n in (6, 7, 8):
            add(f"sympy_sat:n={n}")
    # Prefer concrete local-search continuations at known promising sizes before
    # jumping to broader complete searches at larger carriers.
    for n in candidate_ns:
        if 2 <= n <= 8:
            for seed in (0, 1, 2, 3, 4):
                add(f"local_search:n={n}:seed={seed}")
    for n in unique(model_ns + [4, 5, 6, 7, 8]):
        if 2 <= n <= 8:
            add(f"model_finder_v2:n={n}")
    for n in unique(model_ns + [4, 5, 6]):
        if 2 <= n <= 7:
            add(f"model_finder:n={n}")
    add("poly_ce:tier=2:nmax=13")
    add("structured_ce:max_n=7")
    return out[:8]


def false_route_budget(routes: list[Any], requested_budget: float) -> float:
    """Normalize displayed route budgets to the executor's minimums."""
    budget = float(requested_budget or 0)
    cp_ns: list[int] = []
    sympy_ns: list[int] = []
    v2_ns: list[int] = []
    skew_factors: list[tuple[int, int]] = []
    for route in routes:
        route_l = str(route).lower()
        skew_match = re.search(
            r"(?:skew_product|skew|block_model)(?::|:factor=|=)?(\d+)x(\d+)",
            route_l,
        )
        if skew_match:
            skew_factors.append(
                (int(skew_match.group(1)), int(skew_match.group(2)))
            )
            continue
        m_model = re.search(r"n=?(\d+)", route_l)
        if not m_model:
            continue
        if "cp_sat" in route_l or "cpsat" in route_l or "constraint_sat" in route_l:
            cp_ns.append(int(m_model.group(1)))
        elif "sympy_sat" in route_l or "sympy" in route_l:
            sympy_ns.append(int(m_model.group(1)))
        elif "model_finder_v2" in route_l or "goal_directed" in route_l:
            v2_ns.append(int(m_model.group(1)))
    if cp_ns:
        if max(cp_ns) >= 8:
            budget = max(budget, 24.0)
        elif max(cp_ns) >= 7:
            budget = max(budget, 16.0)
    if v2_ns:
        if max(v2_ns) >= 7:
            budget = max(budget, 45.0)
        elif max(v2_ns) >= 6:
            budget = max(budget, 24.0)
    if sympy_ns and sympy_sat_available():
        # Advisory display floor only, and only when the route can actually
        # run; execution budgets are owned by the caller (see
        # false_model_search_detailed).
        budget = max(budget, 120.0)
    if skew_factors:
        largest = max(control * fiber for control, fiber in skew_factors)
        budget = max(budget, 8.0 if largest > 8 else 4.0)
    return max(3.0, budget)


def assigned_ratio(profile: dict[str, Any] | None) -> float | None:
    if not isinstance(profile, dict):
        return None
    size = profile.get("size")
    assigned = profile.get("assigned_cells")
    try:
        denom = int(size) * int(size)
        return round(float(assigned) / float(denom), 3) if denom > 0 else None
    except Exception:
        return None


def false_trial_highlights(trials: list[dict[str, Any]], continuations: list[str]) -> dict[str, Any]:
    """Compress false-search telemetry into feedback an LLM can act on."""
    status_counts: Counter[str] = Counter()
    template_counts: Counter[str] = Counter()
    tried_routes: list[str] = []
    blocked: Counter[tuple[int, int]] = Counter()
    branched: Counter[tuple[int, int]] = Counter()
    best_progress: dict[str, Any] | None = None
    best_progress_score = -1.0
    propagation_routes: list[dict[str, Any]] = []
    cp_sat_routes: list[dict[str, Any]] = []
    sympy_sat_routes: list[dict[str, Any]] = []
    skew_routes: list[dict[str, Any]] = []

    for trial in trials:
        if not isinstance(trial, dict):
            continue
        route = str(trial.get("route") or "")
        if route:
            tried_routes.append(route)
        status_counts[str(trial.get("status") or "unknown")] += 1
        template = str(trial.get("template") or ("local_search" if "seed" in trial else "model_finder"))
        template_counts[template] += 1

        has_propagation_diag = any(
            key in trial
            for key in (
                "nodes",
                "forced_assignments",
                "contradictions",
                "propagation_checks",
                "top_blocked_cells",
                "top_branch_cells",
                "best_partial_table_profile",
            )
        )
        if has_propagation_diag:
            propagation_routes.append({
                "route": route,
                "status": trial.get("status"),
                "n": trial.get("n"),
                "nodes": trial.get("nodes"),
                "forced_assignments": trial.get("forced_assignments"),
                "contradictions": trial.get("contradictions"),
                "propagation_checks": trial.get("propagation_checks"),
            })
        if template == "cp_sat":
            cp_sat_routes.append({
                "route": route,
                "status": trial.get("status"),
                "n": trial.get("n"),
                "skolem_count": trial.get("skolem_count"),
                "infeasible_skolems": trial.get("cp_sat_infeasible_skolems"),
                "unknown_skolems": trial.get("cp_sat_unknown_skolems"),
                "trials": trial.get("trials"),
            })
        if template == "sympy_sat":
            sympy_sat_routes.append({
                "route": route,
                "status": trial.get("status"),
                "n": trial.get("n"),
                "skolem_count": trial.get("skolem_count"),
                "backend": trial.get("backend"),
                "trials": trial.get("trials"),
            })
        if template == "skew_product":
            skew_routes.append({
                "route": route,
                "status": trial.get("status"),
                "control_size": trial.get("control_size"),
                "fiber_size": trial.get("fiber_size"),
                "carrier_size": trial.get("carrier_size"),
                "backend": trial.get("backend"),
                "iterations": trial.get("iterations"),
                "lifted_h_constraints": trial.get("lifted_h_constraints"),
                "quotient_tables_checked": trial.get(
                    "quotient_tables_checked"
                ),
                "quotient_candidates": trial.get("quotient_candidates"),
                "selector_tuples_checked": trial.get(
                    "selector_tuples_checked"
                ),
                "seconds": trial.get("seconds"),
                "suggested_factorizations": trial.get("suggested_factorizations"),
            })

        for item in trial.get("top_blocked_cells") or []:
            cell = item.get("cell") if isinstance(item, dict) else None
            if isinstance(cell, list) and len(cell) == 2:
                blocked[(int(cell[0]), int(cell[1]))] += int(item.get("count") or 0)
        for item in trial.get("top_branch_cells") or []:
            cell = item.get("cell") if isinstance(item, dict) else None
            if isinstance(cell, list) and len(cell) == 2:
                branched[(int(cell[0]), int(cell[1]))] += int(item.get("count") or 0)

        profile = trial.get("best_partial_table_profile")
        ratio = assigned_ratio(profile)
        if ratio is not None and ratio > best_progress_score:
            best_progress_score = ratio
            best_progress = {
                "route": route,
                "status": trial.get("status"),
                "assigned_ratio": ratio,
                "profile": profile,
            }

    policy: list[str] = []
    if continuations:
        policy.append("Try recommended_next_call first; it is the first untried concrete route.")
    if blocked or branched:
        policy.append("Do not repeat exhausted routes; use hot blocked/branch cells as evidence that the next response should change route family, carrier size, seed, or provide a full table.")
    if best_progress and best_progress.get("assigned_ratio", 0) >= 0.8:
        policy.append("A propagation route reached a nearly complete partial table; a complete counterexample table or one nearby local_search continuation is especially useful.")
    if any((row.get("unknown_skolems") or 0) for row in cp_sat_routes):
        policy.append("An exact cp_sat route reached UNKNOWN rather than infeasible; retry the same carrier with more budget, then move carrier size if it remains unknown.")
    if any(row.get("status") in {"timeout", "unsat_or_timeout"} for row in sympy_sat_routes):
        policy.append("A sympy_sat exact route timed out; retry only one carrier size with a larger budget, or switch to model_finder_v2/local_search using the same carrier.")
    if skew_routes and skew_routes[-1].get("status") in {"family_infeasible", "search_incomplete", "budget"}:
        policy.append("The compact quotient-by-fiber family did not close; try its suggested transposed/larger factorization before abandoning structured extensions.")
    if not policy:
        policy.append("Return one untried false_model_search route or switch to a true-side midpoint/lemma_chain.")

    return {
        "tried_routes": tried_routes[-8:],
        "status_counts": dict(status_counts),
        "template_counts": dict(template_counts),
        "propagation_route_summaries": propagation_routes[-4:],
        "cp_sat_route_summaries": cp_sat_routes[-3:],
        "sympy_sat_route_summaries": sympy_sat_routes[-3:],
        "skew_route_summaries": skew_routes[-3:],
        "hot_blocked_cells": top_counter(blocked, limit=5),
        "hot_branch_cells": top_counter(branched, limit=5),
        "best_partial_progress": best_progress,
        "next_action_policy": policy,
    }


def dual_term(term: Term) -> Term:
    if term[0] == "var":
        return term
    return ("op", dual_term(term[2]), dual_term(term[1]))


def dual_equation(eq: dict[str, Any]) -> dict[str, Any]:
    lhs = dual_term(eq["lhs"])
    rhs = dual_term(eq["rhs"])
    return {
        "text": f"{term_to_str(lhs)} = {term_to_str(rhs)}",
        "variables": list(eq["variables"]),
        "lhs": lhs,
        "rhs": rhs,
    }


def transpose_table(table: list[list[int]]) -> list[list[int]]:
    return [[table[j][i] for j in range(len(table))] for i in range(len(table))]


def structured_counterexample_search(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    *,
    max_n: int = 7,
    time_budget: float = 8.0,
    allow_dual: bool = True,
) -> tuple[int, list[list[int]], str] | None:
    """Deterministic native witness portfolio, including explicit dual closure.

    This replaces the former embedded-reference route. Polynomial/affine and
    exact/stochastic searches remain separate protocol routes so the scheduler
    can attribute their costs and feedback independently.
    """
    deadline = time.monotonic() + max(0.5, time_budget)
    limit = max(2, min(int(max_n), 9))
    for index, table in enumerate(witness_tables()):
        if len(table) <= limit and is_counterexample(h_eq, g_eq, table):
            return len(table), table, f"named_witness:{index}"
    for index, table in enumerate(structured_tables(limit)):
        if time.monotonic() >= deadline:
            return None
        if is_counterexample(h_eq, g_eq, table):
            return len(table), table, f"structured_family:{index}"
    if allow_dual:
        remaining = deadline - time.monotonic()
        if remaining > 0.25:
            found = structured_counterexample_search(
                dual_equation(h_eq),
                dual_equation(g_eq),
                max_n=limit,
                time_budget=remaining,
                allow_dual=False,
            )
            if found is not None:
                n, table, route = found
                transposed = transpose_table(table)
                if is_counterexample(h_eq, g_eq, transposed):
                    return n, transposed, f"dual:{route}"
    return None


def false_model_search_detailed(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    call: dict[str, Any],
    default_budget: float = 8.0,
    *,
    semantic_context: dict[str, Any] | None = None,
):
    if not finite_countermodel_search_allowed(semantic_context):
        state = semantic_status_state(semantic_context or {})
        return None, protocol_state(
            "FalseModelSearchState",
            "finite_search_prohibited",
            "false_model_search",
            tool="false_model_search",
            trials=[],
            semantic_status=state,
            need_hint=state.get("need_hint"),
            suggested_next_actions=state.get("suggested_next_actions"),
        )
    routes = call.get("routes") or []
    budget = float(call.get("budget") or call.get("time_budget") or default_budget)
    if not routes:
        sizes = call.get("sizes") or [5, 6]
        seeds = call.get("seeds") or [0, 1, 2]
        template = str(call.get("template") or "").lower()
        if template in {"model_finder_v2", "goal_directed", "goal_directed_model_finder"}:
            routes = [f"model_finder_v2:n={int(n)}" for n in sizes]
        elif template in {"poly", "poly_ce", "polynomial"}:
            routes = ["poly_ce:tier=2:nmax=13"]
        elif template in {"cp_sat", "cpsat", "constraint_sat"}:
            routes = [f"cp_sat:n={int(n)}" for n in sizes]
        elif template in {"skew_product", "skew", "block_model"}:
            control = int(call.get("control_size") or call.get("quotient_size") or 2)
            fiber = int(call.get("fiber_size") or 3)
            routes = [f"skew_product:{control}x{fiber}"]
        elif template in {"sympy_sat", "sympy", "cnf_sat", "dpll"}:
            routes = [f"sympy_sat:n={int(n)}" for n in sizes]
        elif template in {"structured_ce", "ce_engine", "witness_families"}:
            routes = ["structured_ce:max_n=7"]
        elif template in {"model_finder", "propagation", "constraint_propagation"}:
            routes = [f"model_finder:n={int(n)}" for n in sizes]
        else:
            routes = [f"local_search:n={int(n)}:seed={int(s)}" for n in sizes for s in seeds]
    route_limit = max(1, int(call.get("max_routes") or 8))
    active_routes = list(routes[:route_limit])
    skipped_routes = [str(route) for route in routes[route_limit:]]
    cp_sat_ns = []
    sympy_sat_ns = []
    skew_factors = []
    for route in active_routes:
        route_l = str(route).lower()
        skew_match = re.search(
            r"(?:skew_product|skew|block_model)(?::|:factor=|=)?(\d+)x(\d+)",
            route_l,
        )
        if skew_match:
            skew_factors.append(
                (int(skew_match.group(1)), int(skew_match.group(2)))
            )
            continue
        m_model = re.search(r"n=?(\d+)", route_l)
        if not m_model:
            continue
        if "cp_sat" in route_l or "cpsat" in route_l or "constraint_sat" in route_l:
            cp_sat_ns.append(int(m_model.group(1)))
        elif "sympy_sat" in route_l or "sympy" in route_l:
            sympy_sat_ns.append(int(m_model.group(1)))
    if cp_sat_ns:
        # CP-SAT UNKNOWN states are budget-sensitive. Treat too-small LLM
        # budgets as a syntax/contract weakness, not as mathematical evidence.
        if max(cp_sat_ns) >= 8:
            budget = max(budget, 24.0)
        elif max(cp_sat_ns) >= 7:
            budget = max(budget, 16.0)
    if skew_factors:
        largest = max(control * fiber for control, fiber in skew_factors)
        budget = max(budget, 8.0 if largest > 8 else 4.0)
    # Deliberately no hidden budget floor for sympy_sat here: the caller owns
    # the time contract. solve()'s late portfolio grants the exact-route
    # window explicitly (bounded by remaining solve time), and the route
    # itself returns a clean timeout when its slice is too small.
    per = max(0.5, budget / max(1, len(active_routes)))
    trials: list[dict[str, Any]] = []
    for route in active_routes:
        route_s = str(route)
        route_l = route_s.lower()
        skew_match = re.search(
            r"(?:skew_product|skew|block_model)(?::|:factor=|=)?(\d+)x(\d+)",
            route_l,
        )
        if skew_match:
            control_size = int(skew_match.group(1))
            fiber_size = int(skew_match.group(2))
            status, table, meta = skew_product_counterexample_search(
                h_eq,
                g_eq,
                control_size,
                fiber_size,
                per,
            )
            trials.append({
                "route": route_s,
                "status": status,
                "template": "skew_product",
                **meta,
            })
            if table is not None and is_counterexample(h_eq, g_eq, table):
                return (len(table), table), protocolize_state({
                    "kind": "FalseModelSearchState",
                    "status": "found",
                    "trials": trials,
                    "counterexample_size": len(table),
                    "source": route_s,
                    "witness_style": "quotient_fiber_skew_product",
                    "symbolic_parameters": {
                        "control_size": meta.get("control_size"),
                        "fiber_size": meta.get("fiber_size"),
                        "control_table": meta.get("control_table"),
                        "fiber_parameters": meta.get("fiber_parameters"),
                    },
                }, "false_model_search")
            continue
        if "structured_ce" in route_l or "ce_engine" in route_l or "witness_families" in route_l:
            m_nmax = re.search(r"(?:max_n|nmax)=?(\d+)", route_l)
            max_n = int(m_nmax.group(1)) if m_nmax else 7
            found = structured_counterexample_search(h_eq, g_eq, max_n=max_n, time_budget=per)
            if found is None:
                trials.append({"route": route_s, "status": "no_model", "template": "structured_ce", "max_n": max_n})
                continue
            n, table, source = found
            trials.append({"route": route_s, "status": "found", "template": "structured_ce", "n": n, "source": source})
            return (n, table), protocolize_state({
                "kind": "FalseModelSearchState",
                "status": "found",
                "trials": trials,
                "counterexample_size": n,
                "source": f"{route_s}:{source}",
                "witness_style": "native_structured_family",
            }, "false_model_search")
        if "poly" in route_l:
            m_tier = re.search(r"tier=?(\d+)", route_l)
            m_nmax = re.search(r"nmax=?(\d+)", route_l)
            max_tier = int(m_tier.group(1)) if m_tier else 2
            nmax = int(m_nmax.group(1)) if m_nmax else 13
            result = find_poly_counterexample(h_eq, g_eq, nmax=nmax, time_budget=per, max_tier=max_tier)
            if result is None:
                trials.append({"route": route_s, "status": "no_model", "template": "poly_ce", "nmax": nmax, "max_tier": max_tier})
                continue
            n, table, formula, meta = result
            trials.append({"route": route_s, "status": "found", "template": "poly_ce", "n": n, **meta})
            if is_counterexample(h_eq, g_eq, table):
                return (n, table, formula), protocolize_state({
                    "kind": "FalseModelSearchState",
                    "status": "found",
                    "trials": trials,
                    "counterexample_size": n,
                    "source": route_s,
                    "witness_style": "polynomial_magma",
                    "op_formula": formula,
                }, "false_model_search")
            continue
        if "cp_sat" in route_l or "cpsat" in route_l or "constraint_sat" in route_l:
            m_model = re.search(r"n=?(\d+)", route_l)
            if not m_model:
                continue
            n = int(m_model.group(1))
            if n < 2 or n > 9:
                continue
            status, table, meta = cp_sat_counterexample_search(h_eq, g_eq, n, per)
            trials.append({"route": route_s, "status": status, "template": "cp_sat", **meta})
            if table is not None and is_counterexample(h_eq, g_eq, table):
                return (n, table), protocolize_state({
                    "kind": "FalseModelSearchState",
                    "status": "found",
                    "trials": trials,
                    "counterexample_size": n,
                    "source": route_s,
                    "witness_style": "cp_sat_table",
                }, "false_model_search")
            continue
        if "sympy_sat" in route_l or "sympy" in route_l:
            m_model = re.search(r"n=?(\d+)", route_l)
            if not m_model:
                continue
            n = int(m_model.group(1))
            if n < 5 or n > 8:
                trials.append({"route": route_s, "status": "skipped_size", "template": "sympy_sat", "n": n})
                continue
            status, table, meta = sympy_sat_counterexample_search(h_eq, g_eq, n, per)
            trials.append({"route": route_s, "status": status, "template": "sympy_sat", **meta})
            if table is not None and is_counterexample(h_eq, g_eq, table):
                return (n, table), protocolize_state({
                    "kind": "FalseModelSearchState",
                    "status": "found",
                    "trials": trials,
                    "counterexample_size": n,
                    "source": route_s,
                    "witness_style": "sympy_sat_table",
                }, "false_model_search")
            continue
        if "model_finder_v2" in route_l or "goal_directed" in route_l:
            m_model = re.search(r"n=?(\d+)", route_l)
            if not m_model:
                continue
            n = int(m_model.group(1))
            if n < 2 or n > 8:
                continue
            m_seed = re.search(r"seed=?(\d+)", route_l)
            seed = int(m_seed.group(1)) if m_seed else 0xC0FFEE
            status, table, meta = goal_directed_model_finder(h_eq, g_eq, n, per, seed=seed)
            trials.append({"route": route_s, "status": status, "template": "model_finder_v2", **meta})
            if table is not None and is_counterexample(h_eq, g_eq, table):
                return (n, table), protocolize_state({
                    "kind": "FalseModelSearchState",
                    "status": "found",
                    "trials": trials,
                    "counterexample_size": n,
                    "source": route_s,
                    "witness_style": "goal_directed_table",
                }, "false_model_search")
            continue
        if "model_finder" in route_l or "propagation" in route_l:
            m_model = re.search(r"n=?(\d+)", route_l)
            if not m_model:
                continue
            n = int(m_model.group(1))
            if n < 2 or n > 7:
                continue
            status, table, meta = propagation_model_finder(h_eq, g_eq, n, per)
            trials.append({"route": route_s, "status": status, **meta})
            if table is not None and is_counterexample(h_eq, g_eq, table):
                return (n, table), protocolize_state({
                    "kind": "FalseModelSearchState",
                    "status": "found",
                    "trials": trials,
                    "counterexample_size": n,
                    "source": route_s,
                }, "false_model_search")
            continue
        m = re.search(r"n=?(\d+).*seed=?(\d+)", route_l)
        if not m:
            continue
        n, seed = int(m.group(1)), int(m.group(2))
        if n < 2 or n > 8:
            continue
        table = local_search_route(h_eq, g_eq, n, seed, per)
        trials.append({"route": route_s, "status": "found" if table is not None else "no_model", "n": n, "seed": seed})
        if table is not None and is_counterexample(h_eq, g_eq, table):
            return (n, table), protocolize_state({
                "kind": "FalseModelSearchState",
                "status": "found",
                "trials": trials,
                "counterexample_size": n,
                "source": route_s,
            }, "false_model_search")
    continuations = unique(skipped_routes + false_route_continuations(trials))
    highlights = false_trial_highlights(trials, continuations)
    next_call = {
        "kind": "tool_call",
        "tool": "false_model_search",
        "target": "goal",
        "routes": continuations[:1],
        "budget": false_route_budget(continuations[:1], min(8.0, budget)),
    } if continuations else None
    return None, protocolize_state({
        "kind": "FalseModelSearchState",
        "status": "no_countermodel_found",
        "budget_seconds": budget,
        "route_limit": route_limit,
        "trials": trials,
        "skipped_routes_due_limit": skipped_routes,
        "diagnostic_highlights": highlights,
        "untried_requested_routes": continuations,
        "recommended_next_call": next_call,
        "route_policy": "Prefer one concrete untried route. Use diagnostic_highlights to avoid repeats and decide whether to change seed, carrier size, or route family.",
        "need_hint": "Use diagnostic_highlights. Try recommended_next_call first if present; otherwise change route family/size/seed, provide a complete counterexample_table, or switch to a true-side midpoint/lemma_chain.",
    }, "false_model_search", suggested_next_actions=[next_call] if next_call else None)


def false_model_search(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    call: dict[str, Any],
    default_budget: float = 8.0,
    *,
    semantic_context: dict[str, Any] | None = None,
):
    found, _state = false_model_search_detailed(
        h_eq,
        g_eq,
        call,
        default_budget,
        semantic_context=semantic_context,
    )
    return found


# H-fact graph


def goal_terms(g_eq: dict[str, Any], limit: int = 12) -> list[str]:
    terms = sorted({term_to_str(t) for t in subterms(g_eq["lhs"]) + subterms(g_eq["rhs"])}, key=lambda s: (-len(s), s))
    return terms[:limit]


def unary_terms(v: str) -> list[str]:
    return [v, f"({v} ◇ {v})", f"(({v} ◇ {v}) ◇ {v})", f"({v} ◇ ({v} ◇ {v}))"]


def candidate_h_args(h_eq: dict[str, Any], g_eq: dict[str, Any], limit: int, extra_terms: list[str] | None = None):
    nargs = len(h_eq["variables"])
    if nargs == 0:
        return []
    vars_ = g_eq["variables"] or ["x"]
    terms = unique((extra_terms or []) + goal_terms(g_eq, 14) + [t for v in vars_ for t in unary_terms(v)] + vars_)
    rows: list[tuple[str, ...]] = []
    seen: set[tuple[str, ...]] = set()

    def add(row: tuple[str, ...]):
        if len(row) == nargs and row not in seen:
            seen.add(row)
            rows.append(row)

    if nargs == 1:
        for a in terms:
            add((a,))
            if len(rows) >= limit:
                break
    else:
        for fill in vars_:
            for a in terms:
                for b in terms[:10]:
                    row = [fill] * nargs
                    row[0] = a
                    row[1] = b
                    add(tuple(row))
                    if len(rows) >= limit:
                        return rows
    return rows[:limit]


def render_h_type(h_eq: dict[str, Any], args: tuple[str, ...]) -> tuple[str, str]:
    sub = {v: args[i] for i, v in enumerate(h_eq["variables"])}
    return term_to_str_subst(h_eq["lhs"], sub), term_to_str_subst(h_eq["rhs"], sub)


def match_pattern_term(pattern: Term, target: Term, pattern_vars: set[str], subst: dict[str, str]) -> bool:
    if pattern[0] == "var" and pattern[1] in pattern_vars:
        value = term_to_str(target)
        old = subst.get(pattern[1])
        if old is None:
            subst[pattern[1]] = value
            return True
        return old == value
    if pattern[0] != target[0]:
        return False
    if pattern[0] == "var":
        return pattern[1] == target[1]
    return (
        match_pattern_term(pattern[1], target[1], pattern_vars, subst)
        and match_pattern_term(pattern[2], target[2], pattern_vars, subst)
    )


def direct_lemma_goal_args(lemma_eq: dict[str, Any], g_eq: dict[str, Any]) -> list[tuple[str, ...]]:
    rows: list[tuple[str, ...]] = []
    pattern_vars = set(lemma_eq["variables"])

    def try_add(left_pattern: Term, right_pattern: Term, left_target: Term, right_target: Term) -> None:
        subst: dict[str, str] = {}
        if not match_pattern_term(left_pattern, left_target, pattern_vars, subst):
            return
        if not match_pattern_term(right_pattern, right_target, pattern_vars, subst):
            return
        if all(var in subst for var in lemma_eq["variables"]):
            rows.append(tuple(subst[var] for var in lemma_eq["variables"]))

    try_add(lemma_eq["lhs"], lemma_eq["rhs"], g_eq["lhs"], g_eq["rhs"])
    try_add(lemma_eq["lhs"], lemma_eq["rhs"], g_eq["rhs"], g_eq["lhs"])
    try_add(lemma_eq["rhs"], lemma_eq["lhs"], g_eq["lhs"], g_eq["rhs"])
    try_add(lemma_eq["rhs"], lemma_eq["lhs"], g_eq["rhs"], g_eq["lhs"])
    return unique_arg_rows(rows)


def candidate_lemma_args(lemma_eq: dict[str, Any], g_eq: dict[str, Any], limit: int):
    pool = unique(g_eq["variables"] + goal_terms(g_eq, 12))
    rows: list[tuple[str, ...]] = []

    for row in direct_lemma_goal_args(lemma_eq, g_eq):
        rows.append(row)
        if len(rows) >= limit:
            return unique_arg_rows(rows)

    for row in product(pool, repeat=len(lemma_eq["variables"])):
        rows.append(row)
        if len(rows) >= limit:
            break
    return unique_arg_rows(rows)


def safe_lean_name(raw: Any, fallback: str) -> str:
    base = re.sub(r"[^A-Za-z0-9_']", "_", str(raw or "").strip())
    base = re.sub(r"_+", "_", base).strip("_")
    if not base or not re.match(r"^[A-Za-z_]", base):
        base = fallback
    if base in {"G", "h", "inst", "by", "calc", "have", "intro", "grind"}:
        base = fallback
    return base


def unique_lean_name(raw: Any, fallback: str, used: set[str]) -> str:
    base = safe_lean_name(raw, fallback)
    name = base
    idx = 2
    while name in used:
        name = f"{base}_{idx}"
        idx += 1
    used.add(name)
    return name


def equation_size(eq: dict[str, Any]) -> int:
    def size(t: Term) -> int:
        return 1 if t[0] == "var" else 1 + size(t[1]) + size(t[2])

    return size(eq["lhs"]) + size(eq["rhs"])


def all_tables_2() -> list[list[list[int]]]:
    out = []
    for values in product(range(2), repeat=4):
        out.append([list(values[:2]), list(values[2:])])
    return out


def hint_refutation(h_eq: dict[str, Any], hint_eq: dict[str, Any]) -> dict[str, Any] | None:
    """Find a tiny model of H that refutes the proposed lemma, if obvious."""
    for table in all_tables_2() + witness_tables() + list(structured_tables(3))[:6]:
        if eq_holds(h_eq, table) and not eq_holds(hint_eq, table):
            return {
                "kind": "small_model_refutation",
                "n": len(table),
                "table": table,
                "reason": "table satisfies H but violates the proposed midpoint",
            }
    return None


def hint_score(hint: UniversalEquation, g_eq: dict[str, Any]) -> tuple[int, int, int]:
    goal_subterms = set(goal_terms(g_eq, 24))
    lhs = term_to_str(hint.eq["lhs"])
    rhs = term_to_str(hint.eq["rhs"])
    score = 0
    if lhs in goal_subterms:
        score += 8
    if rhs in goal_subterms:
        score += 8
    if helper_kind(hint.eq["text"]):
        score += 4
    score += len(set(hint.eq["variables"]) & set(g_eq["variables"]))
    return (-score, equation_size(hint.eq), len(hint.eq["variables"]))


def ordered_hints_for_payload(payload: dict[str, Any], hints: list[UniversalEquation], g_eq: dict[str, Any]) -> list[UniversalEquation]:
    kind = payload.get("kind") or payload.get("tool")
    if kind in {"midpoint_chain", "lemma_chain"}:
        return hints
    return sorted(hints, key=lambda hint: hint_score(hint, g_eq))


def hint_rows(value: Any) -> list[tuple[str, ...]]:
    return [
        tuple(str(cell) for cell in row)
        for row in (value or [])
        if isinstance(row, list) and all(isinstance(cell, str) for cell in row)
    ]


def clean_equation_hint_text(raw: str) -> str:
    """Normalize common LLM/Lean wrappers around an equation hint."""
    text = normalize(str(raw)).strip().strip("`")
    text = re.sub(r"^```(?:lean|json)?\s*\n?", "", text)
    text = re.sub(r"\n?```\s*$", "", text)
    text = re.sub(r"--.*$", "", text, flags=re.MULTILINE)
    text = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    text = text.split(":=", 1)[0].strip()
    text = re.sub(r"^\s*(?:lemma|theorem|have)\s+[A-Za-z0-9_']+\s*:\s*", "", text)
    if text.startswith("∀") or text.lower().startswith("forall"):
        parts = re.split(r",", text, maxsplit=1)
        if len(parts) == 2:
            text = parts[1].strip()
    if ":" in text and "=" in text and text.index(":") < text.index("="):
        text = text.split(":", 1)[1].strip()
    text = text.splitlines()[0].strip().rstrip(".;")
    return text


def parse_universal_equations(payload: dict[str, Any]) -> list[UniversalEquation]:
    """Extract LLM-proposed equations. Parsing is triage, not trust."""
    items: list[Any] = []
    payload_seed_rows = hint_rows(payload.get("seed_h_args") or payload.get("seed_args"))
    payload_use_rows = hint_rows(payload.get("use_args") or payload.get("lemma_args"))
    for key in ("lemma", "midpoint", "equation"):
        if isinstance(payload.get(key), str):
            items.append({"equation": payload[key], "name": key})
    for key in ("lemmas", "midpoints", "lemma_chain", "chain", "steps", "equations", "lemma_hints", "hints", "candidates"):
        value = payload.get(key)
        if isinstance(value, str):
            items.append({"equation": value, "name": key})
        elif isinstance(value, list):
            items.extend(value)

    out: list[UniversalEquation] = []
    used: set[str] = set()
    for idx, item in enumerate(items, start=1):
        if isinstance(item, str):
            eq_text = item
            raw_name = f"m{idx}"
            seed_rows: list[tuple[str, ...]] = []
            use_rows: list[tuple[str, ...]] = []
        elif isinstance(item, dict):
            eq_text = item.get("equation") or item.get("lemma") or item.get("claim") or item.get("text")
            raw_name = item.get("name") or item.get("kind") or f"m{idx}"
            seed_rows = hint_rows(item.get("seed_h_args") or item.get("seed_args"))
            if not seed_rows:
                seed_rows = payload_seed_rows
            use_rows = hint_rows(item.get("use_args") or item.get("lemma_args"))
            if not use_rows:
                use_rows = payload_use_rows
        else:
            continue
        if not isinstance(eq_text, str) or "=" not in eq_text:
            continue
        try:
            eq = parse_equation(clean_equation_hint_text(eq_text))
        except Exception:
            continue
        if eq["lhs"] == eq["rhs"] or len(eq["variables"]) > 6 or equation_size(eq) > 40:
            continue
        name = unique_lean_name(raw_name, f"m{idx}", used)
        out.append(UniversalEquation(
            name=name,
            eq=eq,
            extra_args=seed_rows or use_rows,
            seed_args=seed_rows or None,
            use_args=use_rows or None,
        ))
    return out


def render_lemma_type(lemma_eq: dict[str, Any], args: tuple[str, ...]) -> tuple[str, str]:
    sub = {v: args[i] for i, v in enumerate(lemma_eq["variables"])}
    return term_to_str_subst(lemma_eq["lhs"], sub), term_to_str_subst(lemma_eq["rhs"], sub)


def lemma_statement(lemma_eq: dict[str, Any]) -> str:
    lhs, rhs = term_to_str(lemma_eq["lhs"]), term_to_str(lemma_eq["rhs"])
    if not lemma_eq["variables"]:
        return f"{lhs} = {rhs}"
    return f"∀ {' '.join(lemma_eq['variables'])} : G, {lhs} = {rhs}"


def build_graph_facts(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    limit: int = 48,
    lemmas: list[dict[str, Any]] | None = None,
    lemma_limit: int = 96,
    congruence_cap: int = 0,
    extra_terms: list[str] | None = None,
    extra_args: list[tuple[str, ...]] | None = None,
):
    facts: list[dict[str, Any]] = []
    seen: set[tuple[str, str]] = set()

    def add(fact: dict[str, Any]):
        edge = (fact["lhs"], fact["rhs"])
        if edge in seen or (edge[1], edge[0]) in seen:
            return
        seen.add(edge)
        facts.append(fact)

    h_rows = unique_arg_rows(
        list(extra_args or []) + candidate_h_args(h_eq, g_eq, limit, extra_terms=extra_terms)
    )
    for args in h_rows:
        lhs, rhs = render_h_type(h_eq, args)
        add({"name": f"f{len(facts)+1}", "kind": "base", "call": "h " + " ".join(map(lean_arg, args)), "lhs": lhs, "rhs": rhs, "deps": []})

    for lemma in lemmas or []:
        lemma_args = unique_arg_rows(
            list(lemma.get("extra_args") or [])
            + candidate_lemma_args(lemma["eq"], g_eq, lemma_limit)
        )
        for args in lemma_args:
            lhs, rhs = render_lemma_type(lemma["eq"], args)
            add({"name": f"f{len(facts)+1}", "kind": "base", "call": lemma["name"] + " " + " ".join(map(lean_arg, args)), "lhs": lhs, "rhs": rhs, "deps": []})

    if congruence_cap <= 0:
        return facts
    contexts = unique(goal_terms(g_eq, 12) + g_eq["variables"])
    snapshot = list(facts)
    made = 0
    for fact in snapshot:
        for term in contexts:
            if made >= congruence_cap:
                return facts
            if term in (fact["lhs"], fact["rhs"]):
                continue
            add({
                "name": f"f{len(facts)+1}",
                "kind": "congruence",
                "lhs": f"({fact['lhs']} ◇ {term})",
                "rhs": f"({fact['rhs']} ◇ {term})",
                "deps": [fact["name"]],
                "proof": f"by simpa using congrArg (fun __baby_arg => __baby_arg ◇ {term}) {fact['name']}",
            })
            made += 1
            if made >= congruence_cap:
                return facts
            add({
                "name": f"f{len(facts)+1}",
                "kind": "congruence",
                "lhs": f"({term} ◇ {fact['lhs']})",
                "rhs": f"({term} ◇ {fact['rhs']})",
                "deps": [fact["name"]],
                "proof": f"by simpa using congrArg (fun __baby_arg => {term} ◇ __baby_arg) {fact['name']}",
            })
            made += 1
    return facts


def fact_deps(facts_by_name: dict[str, dict[str, Any]], fact: dict[str, Any]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    seen: set[str] = set()

    def visit(name: str):
        if name in seen:
            return
        seen.add(name)
        f = facts_by_name[name]
        for dep in f.get("deps", []):
            visit(dep)
        out.append(f)

    visit(fact["name"])
    return out


def h_graph_body(h_eq: dict[str, Any], g_eq: dict[str, Any], limit: int = 48, lemmas=None, lemma_limit=96, congruence_cap=0, extra_terms=None, extra_args=None):
    facts = build_graph_facts(
        h_eq,
        g_eq,
        limit,
        lemmas=lemmas,
        lemma_limit=lemma_limit,
        congruence_cap=congruence_cap,
        extra_terms=extra_terms,
        extra_args=extra_args,
    )
    facts_by_name = {f["name"]: f for f in facts}
    start = term_to_str(g_eq["lhs"])
    target = term_to_str(g_eq["rhs"])
    adj: dict[str, list[tuple[str, dict[str, Any], bool]]] = {}
    for f in facts:
        adj.setdefault(f["lhs"], []).append((f["rhs"], f, False))
        adj.setdefault(f["rhs"], []).append((f["lhs"], f, True))
    parent: dict[str, tuple[str, dict[str, Any], bool] | None] = {start: None}
    queue = [start]
    while queue and target not in parent:
        cur = queue.pop(0)
        for nxt, fact, rev in adj.get(cur, []):
            if nxt not in parent:
                parent[nxt] = (cur, fact, rev)
                queue.append(nxt)
    if target not in parent:
        return None
    path = []
    node = target
    while parent[node] is not None:
        prev, fact, rev = parent[node]  # type: ignore[misc]
        path.append((prev, node, fact, rev))
        node = prev
    path.reverse()
    intro = "intro " + " ".join(g_eq["variables"]) if g_eq["variables"] else ""
    if not path:
        return intro + "\nrfl"
    used: list[dict[str, Any]] = []
    seen_names: set[str] = set()
    for _, _, fact, _ in path:
        for f in fact_deps(facts_by_name, fact):
            if f["name"] not in seen_names:
                seen_names.add(f["name"])
                used.append(f)
    lines = [intro] if intro else []
    for f in used:
        if f["kind"] == "base":
            lines.append(f"have {f['name']} := {f['call']}")
        else:
            lines.append(f"have {f['name']} : {f['lhs']} = {f['rhs']} := {f['proof']}")
    lines.append("calc")
    for i, (prev, nxt, fact, rev) in enumerate(path):
        lhs = prev if i == 0 else "_"
        suffix = ".symm" if rev else ""
        lines.append(f"  {lhs} = {nxt} := by simpa using {fact['name']}{suffix}")
    return "\n".join(lines)


def short_text(text: str, limit: int = 120) -> str:
    return text if len(text) <= limit else text[: limit - 3] + "..."


def right_context_contraction_actions(h_eq: dict[str, Any], target_eq: dict[str, Any]) -> list[dict[str, Any]]:
    """Suggest reusable helper lemmas for goals differing under one left context."""
    actions: list[dict[str, Any]] = []
    seen: set[str] = set()

    def add_action(lemma: str, left_ctx: Term, simple_right: Term, complex_right: Term, orientation: str) -> None:
        if lemma in seen:
            return
        try:
            lemma_eq = parse_equation(lemma)
        except Exception:
            return
        refutation = hint_refutation(h_eq, lemma_eq)
        if refutation is not None:
            return
        seen.add(lemma)
        actions.append({
            "kind": "midpoint",
            "lemma": lemma,
            "why": (
                "goal differs only in a right argument under the same left prefix; "
                "this reusable contraction can be proved once and then instantiated to the goal"
            ),
            "target_match": {
                "orientation": orientation,
                "left_context": term_to_str(left_ctx),
                "simple_right": term_to_str(simple_right),
                "complex_right": term_to_str(complex_right),
            },
            "refutation_checked": "no_small_countermodel_found",
        })

    def inspect(left_ctx: Term, simple_right: Term, complex_right: Term, orientation: str) -> None:
        # Matches a◇b = a◇((b◇c)◇d), the reusable contraction needed by
        # several row-context goals.
        if (
            simple_right[0] == "var"
            and complex_right[0] == "op"
            and complex_right[1][0] == "op"
            and complex_right[1][1] == simple_right
        ):
            add_action("a ◇ ((b ◇ c) ◇ d) = a ◇ b", left_ctx, simple_right, complex_right, orientation)
        # Also expose the other common bracketing; it is only a suggestion and
        # remains mechanically proved/refuted before use.
        if (
            simple_right[0] == "var"
            and complex_right[0] == "op"
            and complex_right[1] == simple_right
            and complex_right[2][0] == "op"
        ):
            add_action("a ◇ (b ◇ (c ◇ d)) = a ◇ b", left_ctx, simple_right, complex_right, orientation)

    lhs, rhs = target_eq["lhs"], target_eq["rhs"]
    if lhs[0] == "op" and rhs[0] == "op" and lhs[1] == rhs[1]:
        inspect(lhs[1], lhs[2], rhs[2], "lhs_simple_rhs_complex")
        inspect(rhs[1], rhs[2], lhs[2], "rhs_simple_lhs_complex")
    return actions


def goal_generalization_actions(h_eq: dict[str, Any], target_eq: dict[str, Any]) -> list[dict[str, Any]]:
    """Suggest stronger universal lemmas of which the current goal is an instance.

    This is the prompt-side counterpart to the midpoint architecture: the LLM
    should often propose a reusable law rather than the exact goal bridge. The
    suggestions stay untrusted; every returned lemma is still proved from H and
    consumed mechanically before it can affect the answer.
    """
    lhs, rhs = target_eq["lhs"], target_eq["rhs"]
    actions: list[dict[str, Any]] = []
    seen: set[str] = set()

    def left_spine(t: Term) -> Term:
        while t[0] == "op":
            t = t[1]
        return t

    def right_spine(t: Term) -> Term:
        while t[0] == "op":
            t = t[2]
        return t

    def add(card: str, lemma: str, reason: str, *, action_kind: str = "midpoint") -> None:
        if lemma in seen:
            return
        try:
            lemma_eq = parse_equation(lemma)
        except Exception:
            return
        refutation = hint_refutation(h_eq, lemma_eq)
        if refutation is not None:
            return
        seen.add(lemma)
        action: dict[str, Any]
        if action_kind == "standard_aux":
            aux = []
            if lemma == "a ◇ b = a":
                aux = ["proj_l"]
            elif lemma == "a ◇ b = b":
                aux = ["proj_r"]
            elif lemma == "a ◇ b = a ◇ c":
                aux = ["rowconst"]
            elif lemma == "a ◇ b = c ◇ b":
                aux = ["colconst"]
            elif lemma == "a = b":
                aux = ["const"]
            action = {
                "kind": "tool_call",
                "tool": "standard_aux_superposition",
                "target": "goal",
                "lemmas": aux or ["const", "proj_l", "proj_r", "rowconst"],
                "budget": 10,
                "why": reason,
            }
        else:
            action = {"kind": "midpoint", "lemma": lemma, "why": reason}
        actions.append({
            "card": card,
            "lemma": lemma,
            "reason": reason,
            "action": action,
        })

    # Goal is T = A◇T or A◇T = T: right projection is the reusable abstraction.
    if rhs[0] == "op" and rhs[2] == lhs:
        add(
            "generalize_goal_to_right_projection",
            "a ◇ b = b",
            "Goal is a special case of right projection: replace the compound goal term by a fresh variable.",
            action_kind="standard_aux",
        )
    if lhs[0] == "op" and lhs[2] == rhs:
        add(
            "generalize_goal_to_right_projection",
            "a ◇ b = b",
            "Goal is a special case of right projection: prove a reusable projection law, then instantiate it.",
            action_kind="standard_aux",
        )

    # Goal is T = T◇A or T◇A = T: left projection is the reusable abstraction.
    if rhs[0] == "op" and rhs[1] == lhs:
        add(
            "generalize_goal_to_left_projection",
            "a ◇ b = a",
            "Goal is a special case of left projection: replace the repeated outer term by a fresh variable.",
            action_kind="standard_aux",
        )
    if lhs[0] == "op" and lhs[1] == rhs:
        add(
            "generalize_goal_to_left_projection",
            "a ◇ b = a",
            "Goal is a special case of left projection: prove a reusable projection law, then instantiate it.",
            action_kind="standard_aux",
        )

    # Nested projection collapse: under a◇b=a, a whole left-spine tree
    # collapses to its leftmost leaf; under a◇b=b, it collapses to the
    # rightmost leaf. This is often much easier to communicate as a universal
    # lemma than as the exact nested target.
    if rhs[0] == "op" and left_spine(rhs) == lhs:
        add(
            "generalize_nested_goal_to_left_projection",
            "a ◇ b = a",
            "Goal right side has left spine equal to the left side; left projection would collapse the whole tree.",
            action_kind="standard_aux",
        )
    if lhs[0] == "op" and left_spine(lhs) == rhs:
        add(
            "generalize_nested_goal_to_left_projection",
            "a ◇ b = a",
            "Goal left side has left spine equal to the right side; left projection would collapse the whole tree.",
            action_kind="standard_aux",
        )
    if rhs[0] == "op" and right_spine(rhs) == lhs:
        add(
            "generalize_nested_goal_to_right_projection",
            "a ◇ b = b",
            "Goal right side has right spine equal to the left side; right projection would collapse the whole tree.",
            action_kind="standard_aux",
        )
    if lhs[0] == "op" and right_spine(lhs) == rhs:
        add(
            "generalize_nested_goal_to_right_projection",
            "a ◇ b = b",
            "Goal left side has right spine equal to the right side; right projection would collapse the whole tree.",
            action_kind="standard_aux",
        )

    if lhs[0] == "op" and rhs[0] == "op":
        if lhs[1] == rhs[1] and lhs[2] != rhs[2]:
            add(
                "generalize_same_left_to_rowconst",
                "a ◇ b = a ◇ c",
                "Goal has the same left argument on both sides; row-constancy is a stronger reusable bridge.",
                action_kind="standard_aux",
            )
        if lhs[2] == rhs[2] and lhs[1] != rhs[1]:
            add(
                "generalize_same_right_to_colconst",
                "a ◇ b = c ◇ b",
                "Goal has the same right argument on both sides; column-constancy is a stronger reusable bridge.",
            )

    # Sometimes the target does not visibly have same-left shape until H is
    # applied once to the goal's left side. This card lets the LLM ask for a
    # reusable row-constant helper instead of guessing the full superposition
    # derivation.
    if (
        h_eq["lhs"][0] == "op"
        and lhs == h_eq["lhs"]
        and rhs[0] == "op"
    ):
        add(
            "rewrite_with_h_then_rowconst",
            "a ◇ b = a ◇ c",
            "Goal left side matches H's left side; after one H rewrite, row-constancy may bridge the remaining right-argument mismatch.",
            action_kind="standard_aux",
        )

    goal_subs = set(subterms(lhs) + subterms(rhs))
    if any(is_square(t) is not None for t in goal_subs):
        add(
            "square_terms_suggest_square_laws",
            "a ◇ a = b ◇ b",
            "Goal contains square terms; square-constancy is a common reusable midpoint.",
        )

    return actions


def false_feedback_states(mechanical_feedback: list[dict[str, Any]] | None, limit: int | None = 4) -> list[dict[str, Any]]:
    states: list[dict[str, Any]] = []

    def visit(value: Any) -> None:
        if isinstance(value, dict):
            if value.get("source") == "false_model_search" or value.get("kind") == "FalseModelSearchState":
                states.append(value)
            for key in ("tool_state", "state", "native_false_failed_attempts"):
                if key in value:
                    visit(value.get(key))
        elif isinstance(value, list):
            for item in value:
                visit(item)

    visit(mechanical_feedback or [])
    return states[-limit:] if limit is not None else states


def false_tried_routes_from_states(states: list[dict[str, Any]]) -> set[str]:
    routes: set[str] = set()
    for state in states:
        for trial in state.get("trials") or []:
            if isinstance(trial, dict) and trial.get("route") is not None:
                routes.add(str(trial.get("route")))
    return routes


def false_strategy_cards(mechanical_feedback: list[dict[str, Any]] | None) -> list[dict[str, Any]]:
    cards: list[dict[str, Any]] = []
    seen_actions: set[str] = set()
    all_states = false_feedback_states(mechanical_feedback, limit=None)
    states = all_states[-4:]
    tried_routes = false_tried_routes_from_states(all_states)

    def add_card(card: dict[str, Any]) -> None:
        cards.append(card)

    def routes_already_tried(action: dict[str, Any]) -> bool:
        routes = [str(route) for route in action.get("routes") or []]
        return bool(routes) and all(route in tried_routes for route in routes)

    for state in reversed(states):
        next_call = state.get("recommended_next_call")
        if isinstance(next_call, dict):
            action = dict(next_call)
            action_routes = [str(route) for route in action.get("routes") or []]
            if routes_already_tried(action):
                continue
            highlights_for_budget = state.get("diagnostic_highlights") or {}
            cp_unknown_seen = any(
                isinstance(row, dict) and (row.get("unknown_skolems") or 0)
                for row in highlights_for_budget.get("cp_sat_route_summaries") or []
            )
            if cp_unknown_seen and any("cp_sat" in route.lower() for route in action_routes):
                action["budget"] = false_route_budget(action_routes, float(action.get("budget") or 0))
                action["why"] = (
                    "follow false-search recommended_next_call; previous CP-SAT "
                    "route reached UNKNOWN, so give the continuation more budget"
                )
            sig = compact_tool_signature(action)
            if sig not in seen_actions:
                seen_actions.add(sig)
                add_card({
                    "name": "follow_false_recommended_next_call",
                    "principle": "When false-search telemetry gives a concrete untried continuation, try that exact route before inventing another one.",
                    "trigger": "A previous false_model_search route failed but emitted recommended_next_call.",
                    "recommended_action": action,
                })
        highlights = state.get("diagnostic_highlights") or {}
        for row in highlights.get("cp_sat_route_summaries") or []:
            if not isinstance(row, dict) or not (row.get("unknown_skolems") or 0):
                continue
            route = str(row.get("route") or "")
            m = re.search(r"n=?(\d+)", route)
            n = int(m.group(1)) if m else int(row.get("n") or 0)
            retry = {
                "kind": "tool_call",
                "tool": "false_model_search",
                "target": "goal",
                "routes": [f"cp_sat:n={n}"],
                "budget": false_route_budget([f"cp_sat:n={n}"], 16.0),
                "why": "exact CP-SAT reached UNKNOWN; retry same carrier with more budget before changing route family",
            }
            nxt = {
                "kind": "tool_call",
                "tool": "false_model_search",
                "target": "goal",
                "routes": [f"cp_sat:n={min(9, n + 1)}"],
                "budget": false_route_budget([f"cp_sat:n={min(9, n + 1)}"], 16.0),
                "why": "exact CP-SAT reached UNKNOWN; try the next carrier size if the same size remains unknown",
            }
            for action in (retry, nxt):
                if routes_already_tried(action):
                    continue
                sig = compact_tool_signature(action)
                if sig not in seen_actions:
                    seen_actions.add(sig)
                    add_card({
                        "name": "cp_sat_unknown_continuation",
                        "principle": "UNKNOWN is not failure: continue exact finite-domain search with more budget or the next carrier size.",
                        "trigger": f"{route or 'cp_sat'} reached UNKNOWN on {row.get('unknown_skolems')} Skolem branches.",
                        "recommended_action": action,
                    })
        for row in highlights.get("sympy_sat_route_summaries") or []:
            if not isinstance(row, dict) or row.get("status") not in {"timeout", "unsat_or_timeout"}:
                continue
            route = str(row.get("route") or "")
            m = re.search(r"n=?(\d+)", route)
            n = int(m.group(1)) if m else int(row.get("n") or 0)
            if n <= 0:
                continue
            action = {
                "kind": "tool_call",
                "tool": "false_model_search",
                "target": "goal",
                "routes": [f"sympy_sat:n={n}"],
                "budget": false_route_budget([f"sympy_sat:n={n}"], 120.0),
                "why": "sympy exact SAT timed out; retry only this carrier with the full exact-search budget",
            }
            if routes_already_tried(action):
                continue
            sig = compact_tool_signature(action)
            if sig not in seen_actions:
                seen_actions.add(sig)
                add_card({
                    "name": "sympy_sat_timeout_continuation",
                    "principle": "A timed-out exact SAT route is inconclusive; retry a single carrier with a real budget before changing hypothesis.",
                    "trigger": f"{route or 'sympy_sat'} timed out or mixed UNSAT/timeouts.",
                    "recommended_action": action,
                })
        progress = highlights.get("best_partial_progress")
        if isinstance(progress, dict) and (progress.get("assigned_ratio") or 0) >= 0.8:
            route = str(progress.get("route") or "")
            m = re.search(r"n=?(\d+)", route)
            n = int(m.group(1)) if m else None
            if n:
                action = {
                    "kind": "tool_call",
                    "tool": "false_model_search",
                    "target": "goal",
                    "routes": [f"local_search:n={n}:seed=0"],
                    "budget": 10,
                    "why": "propagation reached a nearly complete partial table; try nearby stochastic completions at the same carrier",
                }
                if routes_already_tried(action):
                    continue
                sig = compact_tool_signature(action)
                if sig not in seen_actions:
                    seen_actions.add(sig)
                    add_card({
                        "name": "complete_near_partial_table",
                        "principle": "When propagation nearly fills a table but times out, switch to nearby local_search completions at the same carrier.",
                        "trigger": f"{route} reached assigned_ratio={progress.get('assigned_ratio')}.",
                        "recommended_action": action,
                    })
    def priority(card: dict[str, Any]) -> tuple[int, str]:
        action = card.get("recommended_action") or {}
        routes = [str(route).lower() for route in action.get("routes") or []] if isinstance(action, dict) else []
        if card.get("name") == "follow_false_recommended_next_call" and any("cp_sat" in route or "cpsat" in route for route in routes):
            return (0, str(card.get("name") or ""))
        if any("cp_sat" in route or "cpsat" in route for route in routes):
            return (1, str(card.get("name") or ""))
        if any("sympy_sat" in route or "sympy" in route for route in routes):
            return (1, str(card.get("name") or ""))
        if card.get("name") == "complete_near_partial_table":
            return (2, str(card.get("name") or ""))
        if card.get("name") == "follow_false_recommended_next_call":
            return (3, str(card.get("name") or ""))
        return (4, str(card.get("name") or ""))

    return sorted(cards, key=priority)[:6]


def top_false_recommended_action(mechanical_feedback: list[dict[str, Any]] | None) -> dict[str, Any] | None:
    for card in false_strategy_cards(mechanical_feedback):
        action = card.get("recommended_action")
        if isinstance(action, dict) and action.get("tool") == "false_model_search":
            return action
    return None


def promoted_exact_false_action(mechanical_feedback: list[dict[str, Any]] | None) -> dict[str, Any] | None:
    """Follow a concrete exact-search continuation before asking the LLM.

    This keeps false-side collaboration load-bearing while avoiding a prompt
    when native telemetry has already identified the next exact route.
    """
    states = false_feedback_states(mechanical_feedback, limit=None)
    if not states:
        return None
    highlights = states[-1].get("diagnostic_highlights") or {}
    progress = highlights.get("best_partial_progress") or {}
    try:
        assigned_ratio = float(progress.get("assigned_ratio") or 0.0)
    except Exception:
        assigned_ratio = 0.0
    if assigned_ratio < 0.65:
        return None
    action = top_false_recommended_action(mechanical_feedback)
    if not isinstance(action, dict):
        return None
    routes = [str(route).lower() for route in action.get("routes") or []]
    if any("sympy_sat" in route or "cp_sat" in route or "cpsat" in route for route in routes):
        promoted = dict(action)
        promoted["budget"] = false_route_budget(promoted.get("routes") or [], float(promoted.get("budget") or 0))
        promoted["why"] = "native false telemetry reached a near-complete partial table; follow this exact route before LLM recovery"
        return promoted
    return None


def strategy_cards(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    mechanical_feedback: list[dict[str, Any]] | None = None,
    *,
    prefer_false: bool | str = False,
) -> list[dict[str, Any]]:
    """LLM-facing strategy cards with triggers and concrete protocol actions."""
    cards: list[dict[str, Any]] = []
    for item in goal_generalization_actions(h_eq, g_eq):
        cards.append({
            "name": item["card"],
            "principle": "If G is a special instance of a simpler universal law, try the universal law first.",
            "trigger": item["reason"],
            "recommended_action": item["action"],
        })
    if repeated_self_absorption_h(h_eq, g_eq):
        cards.append({
            "name": "self_absorption_midpoint_chain",
            "principle": (
                "When H rewrites a variable to a term containing repeated copies "
                "of the same variable, a multi-rung absorption chain is often "
                "better than one large direct midpoint."
            ),
            "trigger": "H has x = T with x repeated inside T, and G asks for x = compound.",
            "recommended_action": {
                "kind": "tool_call",
                "tool": "lemma_chain",
                "target": "goal",
                "lemmas": [
                    {"name": "absorb_step", "equation": "<small absorption/contraction equation near a closest_pair>"},
                    {"name": "goal_bridge", "equation": "<second bridge that consumes the first helper toward G>"},
                ],
                "why": "Use SearchState closest_pairs to fill the placeholders; the mechanical side will prove each rung before using it.",
            },
        })
    cards.extend([
        {
            "name": "prefer_reusable_over_goal_specific",
            "principle": "A direct closest-pair bridge may be too specific; prefer a reusable projection, rowconst, opconst, square_const, or contraction law when it would imply G.",
            "recommended_actions": [
                {"kind": "midpoint", "lemma": "a ◇ b = a", "why": "left projection candidate"},
                {"kind": "midpoint", "lemma": "a ◇ b = b", "why": "right projection candidate"},
                {"kind": "midpoint", "lemma": "a ◇ b = a ◇ c", "why": "row-constant candidate"},
                {"kind": "midpoint", "lemma": "a ◇ b = c ◇ d", "why": "operation collapses to a constant product"},
            ],
        },
        {
            "name": "repair_failed_specific_hint",
            "principle": "If a hinted bridge proves but does not close G, strengthen or generalize it; if it is refuted, change family instead of repeating it.",
            "recommended_action": {"kind": "tool_call", "tool": "lemma_chain", "target": "goal", "lemmas": [{"name": "proj_l", "equation": "a ◇ b = a"}, {"name": "proj_r", "equation": "a ◇ b = b"}]},
        },
        {
            "name": "use_feedback_not_transcript",
            "principle": "Use SearchState closest_pairs, proved_not_consumed helpers, and refuted_by_small_model results to choose the next action.",
            "recommended_action": {"kind": "tool_call", "tool": "lemma_hint", "target": "goal", "lemmas": [{"equation": "<non-refuted reusable bridge suggested by feedback>"}]},
        },
    ])
    if prefer_false is True or prefer_false == "balanced":
        cards = false_strategy_cards(mechanical_feedback) + cards
    return cards[:6]


def strategy_cards_text(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    mechanical_feedback: list[dict[str, Any]] | None = None,
    *,
    prefer_false: bool | str = False,
) -> str:
    return json.dumps(strategy_cards(h_eq, g_eq, mechanical_feedback, prefer_false=prefer_false), ensure_ascii=False)


def graph_search_state(
    h_eq: dict[str, Any],
    target_eq: dict[str, Any],
    assumptions: list[UniversalEquation] | None = None,
    *,
    h_limit: int = 80,
    lemma_limit: int = 180,
    congruence_cap: int = 1600,
    status: str = "stuck",
    failed_hints: list[dict[str, Any]] | None = None,
    extra_terms: list[str] | None = None,
    extra_args: list[tuple[str, ...]] | None = None,
) -> dict[str, Any]:
    lemmas = [assumption.as_lemma() for assumption in assumptions or []]
    facts = build_graph_facts(
        h_eq,
        target_eq,
        h_limit,
        lemmas=lemmas,
        lemma_limit=lemma_limit,
        congruence_cap=congruence_cap,
        extra_terms=extra_terms,
        extra_args=extra_args,
    )
    start = term_to_str(target_eq["lhs"])
    target = term_to_str(target_eq["rhs"])
    adj: dict[str, set[str]] = {}
    for fact in facts:
        adj.setdefault(fact["lhs"], set()).add(fact["rhs"])
        adj.setdefault(fact["rhs"], set()).add(fact["lhs"])

    def component(seed: str) -> set[str]:
        seen = {seed}
        queue = [seed]
        while queue:
            cur = queue.pop(0)
            for nxt in adj.get(cur, set()):
                if nxt not in seen:
                    seen.add(nxt)
                    queue.append(nxt)
        return seen

    def sample_terms(terms: set[str], n: int = 6) -> list[str]:
        return [short_text(t) for t in sorted(terms, key=lambda s: (len(s), s))[:n]]

    left_comp = component(start)
    right_comp = component(target)
    left_sample = sample_terms(left_comp)
    right_sample = sample_terms(right_comp)
    pairs: list[dict[str, Any]] = []
    for left in left_sample[:6]:
        for right in right_sample[:6]:
            pairs.append({
                "left": left,
                "right": right,
                "similarity": round(difflib.SequenceMatcher(None, left, right).ratio(), 3),
            })
    pairs.sort(key=lambda p: p["similarity"], reverse=True)
    contraction_actions = right_context_contraction_actions(h_eq, target_eq)
    closest_action = {
        "kind": "midpoint",
        "lemma": f"{pairs[0]['left']} = {pairs[0]['right']}" if pairs else f"{short_text(start)} = {short_text(target)}",
        "why": "candidate bridge between current equality components",
    }
    suggested_next_actions = contraction_actions + ([closest_action] if status != "proved" else [])
    recommended_next_action = suggested_next_actions[0] if suggested_next_actions and status != "proved" else None
    return {
        "protocol_version": PROTOCOL_VERSION,
        "kind": "SearchState",
        "status": status,
        "source": "graph_search",
        "target": target_eq["text"],
        "goal_left": short_text(start),
        "goal_right": short_text(target),
        "attempt": {
            "h_limit": h_limit,
            "lemma_limit": lemma_limit,
            "congruence_cap": congruence_cap,
            "extra_terms": [short_text(t) for t in extra_terms or []][:8],
        },
        "facts_generated": len(facts),
        "assumptions": [
            {"name": assumption.name, "equation": assumption.eq["text"]}
            for assumption in assumptions or []
        ],
        "seed_h_args_used": [list(row) for row in extra_args or []][:8],
        "left_component_size": len(left_comp),
        "right_component_size": len(right_comp),
        "left_frontier": left_sample,
        "right_frontier": right_sample,
        "closest_pairs": pairs[:4],
        "need_hint": {
            "kind": "bridge_terms",
            "left_term": pairs[0]["left"] if pairs else short_text(start),
            "right_term": pairs[0]["right"] if pairs else short_text(target),
            "reason": "would connect the target equality components",
            "recommended_next_action": recommended_next_action,
        },
        "suggested_next_actions": suggested_next_actions if status != "proved" else [],
        "failed_hints": failed_hints or [],
    }


# Proof-carrying superposition core.  This implementation is maintained here
# and has no runtime dependency on another solver.


def term_size(t: Term) -> int:
    return 1 if t[0] == "var" else 1 + term_size(t[1]) + term_size(t[2])


def term_key(t: Term) -> str:
    return t[1] if t[0] == "var" else "(" + term_key(t[1]) + term_key(t[2]) + ")"


NATIVE_SATURATION_CONFIGS: tuple[tuple[int, int, int, int], ...] = (
    (2, 10, 1, 16),
    (2, 10, 2, 24),
    (3, 14, 2, 40),
    (3, 14, 3, 48),
)


def instantiate_term(t: Term, subst: dict[str, Term]) -> Term:
    if t[0] == "var":
        return subst.get(t[1], t)
    return ("op", instantiate_term(t[1], subst), instantiate_term(t[2], subst))


def native_saturation_combos(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    *,
    depth: int,
    pool_cap: int,
    slots: int,
) -> list[tuple[Term, ...]]:
    """Grow H-instantiations from goal subterms with a small bounded closure."""
    h_vars = list(h_eq["variables"])
    if not h_vars:
        return []
    goal_vars = list(g_eq["variables"])
    if not goal_vars:
        return []
    pad: Term = ("var", goal_vars[0])
    pool = sorted(
        set(subterms(g_eq["lhs"]) + subterms(g_eq["rhs"])),
        key=lambda term: (term_size(term), term_key(term)),
    )
    rows: list[tuple[Term, ...]] = []
    seen_rows: set[tuple[Term, ...]] = set()

    def add_row(row: tuple[Term, ...]) -> None:
        if row not in seen_rows:
            seen_rows.add(row)
            rows.append(row)

    for _round in range(max(1, depth)):
        new_terms: set[Term] = set()
        round_rows: list[tuple[Term, ...]] = []
        current = list(pool)
        for position in range(min(max(1, slots), len(h_vars))):
            for term in current:
                row = [pad for _ in h_vars]
                row[position] = term
                round_rows.append(tuple(row))
        round_rows.append(tuple(pad for _ in h_vars))

        for row in round_rows:
            if row in seen_rows:
                continue
            add_row(row)
            subst = dict(zip(h_vars, row))
            new_terms.update(subterms(instantiate_term(h_eq["rhs"], subst)))
        pool = sorted(set(pool) | new_terms, key=lambda term: (term_size(term), term_key(term)))[:max(1, pool_cap)]
    return rows


def native_saturation_bodies(h_eq: dict[str, Any], g_eq: dict[str, Any]):
    """Yield progressively stronger, judgeable saturation certificates."""
    goal_vars = list(g_eq["variables"])
    if not goal_vars or not h_eq["variables"]:
        return
    intro = "intro " + " ".join(goal_vars)
    seen: set[str] = set()
    for depth, pool_cap, slots, have_cap in NATIVE_SATURATION_CONFIGS:
        rows = native_saturation_combos(
            h_eq,
            g_eq,
            depth=depth,
            pool_cap=pool_cap,
            slots=slots,
        )[:have_cap]
        if not rows:
            continue
        haves = [
            f"have sat{i} := h " + " ".join(lean_arg(term_to_str(term)) for term in row)
            for i, row in enumerate(rows, start=1)
        ]
        body = "\n".join([intro, *haves, "grind"])
        if body in seen:
            continue
        seen.add(body)
        yield f"deep_saturation:d={depth}:slots={slots}:haves={len(rows)}", body


def grounding_h_certificate_bodies(h_eq: dict[str, Any], g_eq: dict[str, Any]):
    """Ground both exclusive sides of a non-orientable H, then flood lightly.

    This is the minimal native form of the former generic grounding/collapse
    certificate family.  Every emitted body is still accepted only after the
    Lean judge checks it.
    """
    lhs_vars = set(term_variables(h_eq["lhs"]))
    rhs_vars = set(term_variables(h_eq["rhs"]))
    only_l = lhs_vars - rhs_vars
    only_r = rhs_vars - lhs_vars
    goal_vars = list(g_eq["variables"])
    if not only_l or not only_r or not goal_vars:
        return

    witness = goal_vars[0]
    lhs_binders = [v for v in h_eq["variables"] if v in lhs_vars]
    rhs_binders = [v for v in h_eq["variables"] if v in rhs_vars]
    args_a = [witness if v in only_r else v for v in h_eq["variables"]]
    args_b = [witness if v in only_l else v for v in h_eq["variables"]]
    lhs_grounded = term_to_str_subst(h_eq["lhs"], {v: witness for v in only_r})
    rhs_grounded = term_to_str_subst(h_eq["rhs"], {v: witness for v in only_r})
    lhs_grounded_b = term_to_str_subst(h_eq["lhs"], {v: witness for v in only_l})
    rhs_grounded_b = term_to_str_subst(h_eq["rhs"], {v: witness for v in only_l})

    prefix = ["intro " + " ".join(goal_vars)]
    prefix.extend([
        f"have groundA : ∀ {' '.join(lhs_binders)} : G, {lhs_grounded} = {rhs_grounded} := "
        f"fun {' '.join(lhs_binders)} => h {' '.join(map(lean_arg, args_a))}",
        f"have groundB : ∀ {' '.join(rhs_binders)} : G, {rhs_grounded_b} = {lhs_grounded_b} := "
        f"fun {' '.join(rhs_binders)} => (h {' '.join(map(lean_arg, args_b))}).symm",
    ])
    yield "grounding_h:base", "\n".join([*prefix, "grind"])

    flood_terms = list(goal_vars)
    flood_tiers = [
        flood_terms + [f"({witness} ◇ {witness})"],
        flood_terms + [f"({witness} ◇ {witness})", f"({witness} ◇ ({witness} ◇ {witness}))"],
    ]
    accumulated: list[str] = []
    have_index = 0
    for tier_index, terms in enumerate(flood_tiers, start=1):
        for lemma_name, binders in (("groundA", lhs_binders), ("groundB", rhs_binders)):
            emitted = 0
            for args in product(terms, repeat=len(binders)):
                have_index += 1
                emitted += 1
                accumulated.append(
                    f"have ground_use{have_index} := {lemma_name} "
                    + " ".join(map(lean_arg, args))
                )
                if emitted >= 128:
                    break
        yield f"grounding_h:flood={tier_index}", "\n".join([*prefix, *accumulated, "grind"])


def pc_canon(l: Term, r: Term) -> tuple[Term, Term]:
    if term_size(l) > term_size(r) or (term_size(l) == term_size(r) and term_key(l) > term_key(r)):
        l, r = r, l
    ren: dict[str, Term] = {}

    def go(t: Term) -> Term:
        if t[0] == "var":
            if str(t[1]).startswith("#"):
                return t
            if t[1] not in ren:
                ren[t[1]] = ("var", f"v{len(ren)}")
            return ren[t[1]]
        return ("op", go(t[1]), go(t[2]))

    return go(l), go(r)


def pc_walk(t: Term, sub: dict[str, Term]) -> Term:
    while t[0] == "var" and t[1] in sub:
        t = sub[t[1]]
    return t


def pc_occurs(v: str, t: Term, sub: dict[str, Term]) -> bool:
    t = pc_walk(t, sub)
    if t[0] == "var":
        return t[1] == v
    return pc_occurs(v, t[1], sub) or pc_occurs(v, t[2], sub)


def pc_unify(s: Term, t: Term, sub: dict[str, Term]) -> dict[str, Term] | None:
    s = pc_walk(s, sub)
    t = pc_walk(t, sub)
    if s[0] == "var" and not str(s[1]).startswith("#"):
        if s == t:
            return sub
        if pc_occurs(s[1], t, sub):
            return None
        sub2 = dict(sub)
        sub2[s[1]] = t
        return sub2
    if t[0] == "var" and not str(t[1]).startswith("#"):
        return pc_unify(t, s, sub)
    if s[0] == "op" and t[0] == "op":
        sub2 = pc_unify(s[1], t[1], sub)
        return None if sub2 is None else pc_unify(s[2], t[2], sub2)
    return sub if s == t else None


def pc_apply(t: Term, sub: dict[str, Term]) -> Term:
    t = pc_walk(t, sub)
    if t[0] == "var":
        return t
    return ("op", pc_apply(t[1], sub), pc_apply(t[2], sub))


def pc_positions(t: Term, p: tuple[int, ...] = ()) -> list[tuple[tuple[int, ...], Term]]:
    out = [(p, t)]
    if t[0] == "op":
        out += pc_positions(t[1], p + (0,))
        out += pc_positions(t[2], p + (1,))
    return out


def pc_replace_at(t: Term, p: tuple[int, ...], r: Term) -> Term:
    if not p:
        return r
    if p[0] == 0:
        return ("op", pc_replace_at(t[1], p[1:], r), t[2])
    return ("op", t[1], pc_replace_at(t[2], p[1:], r))


def pc_vars_of(t: Term, acc: list[str] | None = None) -> list[str]:
    acc = acc if acc is not None else []
    if t[0] == "var":
        if not str(t[1]).startswith("#") and t[1] not in acc:
            acc.append(t[1])
    else:
        pc_vars_of(t[1], acc)
        pc_vars_of(t[2], acc)
    return acc


def pc_apply_names(t: Term, rho: dict[str, str]) -> Term:
    if t[0] == "var":
        return ("var", rho.get(t[1], t[1]))
    return ("op", pc_apply_names(t[1], rho), pc_apply_names(t[2], rho))


def pc_rename_tracked(binders: list[str], lhs: Term, rhs: Term, counter: list[int]) -> tuple[list[str], Term, Term]:
    ren = {v: f"_s{counter[0] + i}" for i, v in enumerate(binders)}
    counter[0] += len(binders)

    def go(t: Term) -> Term:
        return ("var", ren[t[1]]) if t[0] == "var" else ("op", go(t[1]), go(t[2]))

    return [ren[v] for v in binders], go(lhs), go(rhs)


def pc_paramodulants(rec_a: dict[str, Any], rec_b: dict[str, Any], counter: list[int], max_size: int, allow_var_overlap: bool = False):
    fb_a, la_a, ra_a = pc_rename_tracked(rec_a["binders"], rec_a["lhs"], rec_a["rhs"], counter)
    fb_b, la_b, ra_b = pc_rename_tracked(rec_b["binders"], rec_b["lhs"], rec_b["rhs"], counter)
    out = []
    for la, ra, a_symm in ((la_a, ra_a, False), (ra_a, la_a, True)):
        for lb, rb, b_symm in ((la_b, ra_b, False), (ra_b, la_b, True)):
            for pos, subterm in pc_positions(la):
                if subterm[0] == "var" and not allow_var_overlap:
                    continue
                subst = pc_unify(subterm, lb, {})
                if subst is None:
                    continue
                rl = pc_apply(pc_replace_at(la, pos, rb), subst)
                rr = pc_apply(ra, subst)
                if rl == rr or term_size(rl) + term_size(rr) > max_size:
                    continue
                args_a = [pc_apply(("var", fb_a[k]), subst) for k in range(len(rec_a["binders"]))]
                args_b = [pc_apply(("var", fb_b[k]), subst) for k in range(len(rec_b["binders"]))]
                all_vars: list[str] = []
                for t in [rl, rr] + args_a + args_b:
                    for v in pc_vars_of(t):
                        if v not in all_vars:
                            all_vars.append(v)
                rho = {v: f"v{k}" for k, v in enumerate(all_vars)}
                cl = lambda t: pc_apply_names(t, rho)
                before = cl(pc_apply(la, subst))
                source_l = cl(pc_apply(lb, subst))
                source_r = cl(pc_apply(rb, subst))
                out.append((
                    cl(rl),
                    cl(rr),
                    [f"v{k}" for k in range(len(all_vars))],
                    [cl(a) for a in args_a],
                    [cl(a) for a in args_b],
                    {
                        "before": before,
                        "source_l": source_l,
                        "source_r": source_r,
                        "pos": pos,
                        "a_symm": a_symm,
                        "b_symm": b_symm,
                    },
                ))
    return out


def pc_saturate(
    start: list[tuple[Term, Term]],
    target,
    max_rounds: int = 5,
    max_eqs: int = 900,
    max_size: int = 20,
    time_budget: float | None = None,
    allow_var_overlap: bool = False,
) -> tuple[int | None, list[dict[str, Any]], dict[str, Any]]:
    deadline = (time.monotonic() + time_budget) if time_budget else None
    counter = [0]
    recs: list[dict[str, Any]] = []
    seen: dict[tuple[str, str], int] = {}
    meta = {"rounds": 0, "stop_reason": "saturated", "max_rounds": max_rounds, "max_eqs": max_eqs, "max_size": max_size}

    def add(l: Term, r: Term, binders: list[str], deriv, base=None) -> int | None:
        cl, cr = pc_canon(l, r)
        if cl == cr:
            return None
        sig = (term_key(cl), term_key(cr))
        if sig in seen:
            return seen[sig]
        rid = len(recs)
        recs.append({"lhs": l, "rhs": r, "binders": binders, "deriv": deriv, "base": base})
        seen[sig] = rid
        return rid

    for i, (l, r) in enumerate(start):
        binders = pc_vars_of(l) + [v for v in pc_vars_of(r) if v not in pc_vars_of(l)]
        rid = add(l, r, binders, None, i)
        if rid is not None and target((recs[rid]["lhs"], recs[rid]["rhs"])):
            meta["stop_reason"] = "target_found"
            return rid, recs, meta
    for round_idx in range(max_rounds):
        meta["rounds"] = round_idx + 1
        added = False
        ids = list(range(len(recs)))
        for i in ids:
            if deadline is not None and time.monotonic() > deadline:
                meta["stop_reason"] = "time_budget"
                return None, recs, meta
            for j in ids:
                for rl, rr, binders, args_a, args_b, proof_info in pc_paramodulants(
                    recs[i],
                    recs[j],
                    counter,
                    max_size,
                    allow_var_overlap=allow_var_overlap,
                ):
                    before = len(recs)
                    rid = add(rl, rr, binders, (i, j, args_a, args_b, proof_info))
                    if rid is not None and rid == before:
                        added = True
                        if target((recs[rid]["lhs"], recs[rid]["rhs"])):
                            meta["stop_reason"] = "target_found"
                            return rid, recs, meta
        if not added:
            meta["stop_reason"] = "saturated"
            break
        if len(recs) > max_eqs:
            meta["stop_reason"] = "max_eqs"
            break
    return None, recs, meta


def pc_derivation_chain(target_id: int, recs: list[dict[str, Any]]) -> list[int]:
    need: set[int] = set()
    order: list[int] = []

    def visit(rid: int) -> None:
        if rid in need:
            return
        deriv = recs[rid]["deriv"]
        if deriv is not None:
            visit(deriv[0])
            visit(deriv[1])
        need.add(rid)
        order.append(rid)

    visit(target_id)
    return order


def pc_arg(t: Term) -> str:
    return t[1] if t[0] == "var" else f"({term_to_str(t)})"


def pc_term_with_hole(t: Term, pos: tuple[int, ...], hole: str = "__pc_hole") -> str:
    if not pos:
        return hole
    if t[0] == "var":
        return term_to_str(t)
    if pos[0] == 0:
        return f"({pc_term_with_hole(t[1], pos[1:], hole)} ◇ {term_to_str(t[2])})"
    return f"({term_to_str(t[1])} ◇ {pc_term_with_hole(t[2], pos[1:], hole)})"


def pc_oriented_expr(name: str, symm: bool) -> str:
    return f"({name}).symm" if symm else name


def pc_match_term(pat: Term, val: Term, binders: set[str], sub: dict[str, Term]) -> dict[str, Term] | None:
    if pat[0] == "var" and pat[1] in binders:
        old = sub.get(pat[1])
        if old is None:
            sub2 = dict(sub)
            sub2[pat[1]] = val
            return sub2
        return sub if old == val else None
    if pat[0] == "op" and val[0] == "op":
        s1 = pc_match_term(pat[1], val[1], binders, sub)
        return None if s1 is None else pc_match_term(pat[2], val[2], binders, s1)
    return sub if pat == val else None


def pc_target_proof_expr(name: str, lhs_pat: Term, rhs_pat: Term, binders: list[str], goal_lhs: Term | None, goal_rhs: Term | None) -> str | None:
    if goal_lhs is None or goal_rhs is None or not binders:
        return None

    def try_match(a: Term, b: Term, symm: bool) -> str | None:
        sub = pc_match_term(lhs_pat, a, set(binders), {})
        if sub is None:
            return None
        sub = pc_match_term(rhs_pat, b, set(binders), sub)
        if sub is None or any(v not in sub for v in binders):
            return None
        args = " ".join(pc_arg(sub[v]) for v in binders)
        call = f"{name} {args}" if args else name
        return f"({call}).symm" if symm else call

    return try_match(goal_lhs, goal_rhs, False) or try_match(goal_rhs, goal_lhs, True)


def pc_target_exact_line(name: str, lhs_pat: Term, rhs_pat: Term, binders: list[str], goal_lhs: Term | None, goal_rhs: Term | None) -> str | None:
    expr = pc_target_proof_expr(name, lhs_pat, rhs_pat, binders, goal_lhs, goal_rhs)
    return None if expr is None else f"exact {expr}"


def pc_subst_term(t: Term, sub: dict[str, Term]) -> Term:
    if t[0] == "var" and t[1] in sub:
        return sub[t[1]]
    if t[0] == "op":
        return ("op", pc_subst_term(t[1], sub), pc_subst_term(t[2], sub))
    return t


def pc_stitch_pool(goal_lhs: Term | None, goal_rhs: Term | None, limit: int = 14) -> list[Term]:
    out: list[Term] = []
    seen: set[str] = set()
    for root in (goal_lhs, goal_rhs):
        if root is None:
            continue
        for t in subterms(root):
            sig = term_key(t)
            if sig not in seen:
                seen.add(sig)
                out.append(t)
    out.sort(key=lambda t: (term_size(t), term_key(t)))
    return out[:limit]


def pc_bounded_completions(base: dict[str, Term], binders: list[str], pool: list[Term], max_missing: int = 3, max_total: int = 350):
    rem = [v for v in binders if v not in base]
    if len(rem) > max_missing:
        return
    seen: set[tuple[str, ...]] = set()
    total = 0
    for vals in product(pool, repeat=len(rem)):
        sub = dict(base)
        for v, val in zip(rem, vals):
            sub[v] = val
        sig = tuple(term_key(sub[v]) for v in binders)
        if sig in seen:
            continue
        seen.add(sig)
        yield sub
        total += 1
        if total >= max_total:
            return


def pc_lemma_edges_from(term: Term, lhs_pat: Term, rhs_pat: Term, binders: list[str], pool: list[Term], name: str, max_missing: int = 3):
    bset = set(binders)
    for side in (0, 1):
        pat = lhs_pat if side == 0 else rhs_pat
        other = rhs_pat if side == 0 else lhs_pat
        base = pc_match_term(pat, term, bset, {})
        if base is None:
            continue
        for sub in pc_bounded_completions(base, binders, pool, max_missing=max_missing):
            out = pc_subst_term(other, sub)
            if out == term:
                continue
            args = " ".join(pc_arg(sub[v]) for v in binders)
            call = f"{name} {args}" if args else name
            proof = call if side == 0 else f"({call}).symm"
            yield out, proof


def pc_add_subterms_to_pool(pool: list[Term], seen: set[str], term: Term, limit: int) -> None:
    for t in subterms(term):
        sig = term_key(t)
        if sig not in seen:
            seen.add(sig)
            pool.append(t)
            if len(pool) >= limit:
                return


def pc_one_h_target_calc(
    hrec: dict[str, Any] | None,
    target_lhs: Term,
    target_rhs: Term,
    target_binders: list[str],
    goal_lhs: Term | None,
    goal_rhs: Term | None,
    h_name: str = "h",
    target_name: str = "target",
) -> str | None:
    if goal_lhs is None or goal_rhs is None or not hrec or not target_binders:
        return None
    hvars = hrec.get("binders") or []
    if not hvars:
        return None
    pool = pc_stitch_pool(goal_lhs, goal_rhs)
    if not pool:
        return None

    def complete(base: dict[str, Term]):
        rem = [v for v in hvars if v not in base]
        if len(rem) > 4:
            return
        seen: set[tuple[str, ...]] = set()
        for vals in product(pool, repeat=len(rem)):
            sub = dict(base)
            for v, val in zip(rem, vals):
                sub[v] = val
            sig = tuple(term_key(sub[v]) for v in hvars)
            if sig in seen:
                continue
            seen.add(sig)
            yield sub

    def h_call(sub: dict[str, Term]) -> str:
        return f"{h_name} " + " ".join(pc_arg(sub[v]) for v in hvars)

    for side, endpoint in ((0, goal_lhs), (1, goal_lhs), (0, goal_rhs), (1, goal_rhs)):
        hside = hrec["lhs"] if side == 0 else hrec["rhs"]
        base = pc_match_term(hside, endpoint, set(hvars), {})
        if base is None:
            continue
        for sub in complete(base):
            hl = pc_subst_term(hrec["lhs"], sub)
            hr = pc_subst_term(hrec["rhs"], sub)
            call = h_call(sub)
            if side == 0 and hl != endpoint:
                continue
            if side == 1 and hr != endpoint:
                continue
            if endpoint == goal_lhs:
                mid = hr if side == 0 else hl
                p1 = call if side == 0 else f"({call}).symm"
                p2 = pc_target_proof_expr(target_name, target_lhs, target_rhs, target_binders, mid, goal_rhs)
                if p2 is not None:
                    return "\n".join([
                        "calc",
                        f"  {term_to_str(goal_lhs)} = {term_to_str(mid)} := {p1}",
                        f"  _ = {term_to_str(goal_rhs)} := {p2}",
                    ])
            else:
                mid = hr if side == 0 else hl
                p1 = pc_target_proof_expr(target_name, target_lhs, target_rhs, target_binders, goal_lhs, mid)
                p2 = f"({call}).symm" if side == 0 else call
                if p1 is not None:
                    return "\n".join([
                        "calc",
                        f"  {term_to_str(goal_lhs)} = {term_to_str(mid)} := {p1}",
                        f"  _ = {term_to_str(goal_rhs)} := {p2}",
                    ])
    return None


def pc_path_target_calc(
    hrec: dict[str, Any] | None,
    target_lhs: Term,
    target_rhs: Term,
    target_binders: list[str],
    goal_lhs: Term | None,
    goal_rhs: Term | None,
    h_name: str = "h",
    target_name: str = "target",
) -> str | None:
    if goal_lhs is None or goal_rhs is None or not target_binders:
        return None
    hvars = (hrec or {}).get("binders") or []
    pool = pc_stitch_pool(goal_lhs, goal_rhs, limit=16)
    pool_seen = {term_key(t) for t in pool}
    target_key = term_key(goal_rhs)
    start_key = term_key(goal_lhs)
    nodes = {start_key: goal_lhs}
    parent: dict[str, tuple[str, str] | None] = {start_key: None}
    queue = [goal_lhs]
    max_nodes, max_depth, qi = 120, 5, 0

    def depth_of(k: str) -> int:
        depth = 0
        while parent.get(k) is not None:
            k = parent[k][0]  # type: ignore[index]
            depth += 1
        return depth

    while qi < len(queue) and len(nodes) < max_nodes:
        cur = queue[qi]
        qi += 1
        ck = term_key(cur)
        if ck == target_key:
            break
        if depth_of(ck) >= max_depth:
            continue
        edges = list(pc_lemma_edges_from(cur, target_lhs, target_rhs, target_binders, pool, target_name, max_missing=3))
        if hrec is not None and hvars:
            edges.extend(pc_lemma_edges_from(cur, hrec["lhs"], hrec["rhs"], hvars, pool, h_name, max_missing=3))
        for nxt, proof in edges:
            nk = term_key(nxt)
            if nk in nodes or term_size(nxt) > 18:
                continue
            nodes[nk] = nxt
            parent[nk] = (ck, proof)
            queue.append(nxt)
            pc_add_subterms_to_pool(pool, pool_seen, nxt, 24)
            if nk == target_key:
                qi = len(queue)
                break
    if target_key not in parent:
        return None
    path = []
    k = target_key
    while parent[k] is not None:
        pk, proof = parent[k]  # type: ignore[misc]
        path.append((nodes[pk], nodes[k], proof))
        k = pk
    path.reverse()
    if not path:
        return None
    lines = ["calc"]
    for i, (a, b, proof) in enumerate(path):
        lines.append(f"  {term_to_str(a) if i == 0 else '_'} = {term_to_str(b)} := {proof}")
    return "\n".join(lines)


def pc_render_step_body(rec: dict[str, Any], ia_line: str, ib_line: str) -> str:
    deriv = rec["deriv"]
    if deriv is None:
        raise ValueError("base record has no renderable step")
    proof_info = deriv[4] if len(deriv) >= 5 else None
    binders = " ".join(rec["binders"])
    intro = f"intro {binders}; " if binders else ""
    if not proof_info:
        return f"by {intro}{ia_line}; {ib_line}; grind"
    before = proof_info["before"]
    pos = tuple(proof_info["pos"])
    context = pc_term_with_hole(before, pos)
    ib_expr = pc_oriented_expr("ib", bool(proof_info.get("b_symm")))
    ia_expr = pc_oriented_expr("ia", bool(proof_info.get("a_symm")))
    before_s = term_to_str(before)
    after_s = term_to_str(rec["lhs"])
    return (
        f"by {intro}{ia_line}; {ib_line}; "
        f"have step : {before_s} = {after_s} := "
        f"congrArg (fun __pc_hole => {context}) ({ib_expr}); "
        f"exact step.symm.trans ({ia_expr})"
    )


def pc_render(
    target_id: int,
    recs: list[dict[str, Any]],
    goal_vars: list[str],
    goal_lhs: Term | None = None,
    goal_rhs: Term | None = None,
    base_names: list[str] | None = None,
) -> str:
    base_names = base_names or ["h"]

    def lemma_name(rid: int) -> str:
        if recs[rid]["deriv"] is not None:
            return f"E{rid}"
        base = recs[rid].get("base")
        if isinstance(base, int) and 0 <= base < len(base_names):
            return base_names[base]
        return "h"

    order = pc_derivation_chain(target_id, recs)
    lines = ["intro " + " ".join(goal_vars)] if goal_vars else []
    for rid in order:
        rec = recs[rid]
        if rec["deriv"] is None:
            continue
        ai, bi, args_a, args_b = rec["deriv"][:4]
        an = lemma_name(ai)
        bn = lemma_name(bi)
        binders = rec["binders"]
        ia = f"have ia := {an} " + " ".join(pc_arg(x) for x in args_a) if args_a else f"have ia := {an}"
        ib = f"have ib := {bn} " + " ".join(pc_arg(x) for x in args_b) if args_b else f"have ib := {bn}"
        lhs = term_to_str(rec["lhs"])
        rhs = term_to_str(rec["rhs"])
        binder_chunk = " ".join(binders)
        lines.append(
            f"have E{rid} : ∀ ({binder_chunk} : G), {lhs} = {rhs} := "
            f"{pc_render_step_body(rec, ia, ib)}"
        )
    target_rec = recs[target_id]
    if target_rec["deriv"] is not None:
        ess = pc_vars_of(target_rec["lhs"])
        for v in pc_vars_of(target_rec["rhs"]):
            if v not in ess:
                ess.append(v)
        exact_line = pc_target_exact_line("target", target_rec["lhs"], target_rec["rhs"], ess, goal_lhs, goal_rhs)
        hrec = None
        for rec in recs:
            if rec["deriv"] is None:
                base = rec.get("base")
                if base is None or (isinstance(base, int) and base < len(base_names) and base_names[base] == "h"):
                    hrec = rec
                    break
        calc_line = pc_one_h_target_calc(hrec, target_rec["lhs"], target_rec["rhs"], ess, goal_lhs, goal_rhs)
        if calc_line is None:
            calc_line = pc_path_target_calc(hrec, target_rec["lhs"], target_rec["rhs"], ess, goal_lhs, goal_rhs)
        if ess and (len(ess) < len(target_rec["binders"]) or exact_line is not None or calc_line is not None):
            d0 = ess[0]
            args = " ".join(v if v in ess else d0 for v in target_rec["binders"])
            lhs = term_to_str(target_rec["lhs"])
            rhs = term_to_str(target_rec["rhs"])
            lines.append(
                f"have target : ∀ ({' '.join(ess)} : G), {lhs} = {rhs} := "
                f"fun {' '.join(ess)} => E{target_id} {args}"
            )
            if exact_line is not None:
                lines.append(exact_line)
                return "\n".join(lines)
            if calc_line is not None:
                lines.append(calc_line)
                return "\n".join(lines)
    lines.append("grind")
    return "\n".join(lines)


def pc_rec_summary(rec: dict[str, Any]) -> dict[str, Any]:
    return {
        "lhs": short_text(term_to_str(rec["lhs"]), 120),
        "rhs": short_text(term_to_str(rec["rhs"]), 120),
        "binders": rec.get("binders", [])[:6],
        "derived": rec.get("deriv") is not None,
    }


def collapse_witness_vars(t: Term, acc: set[str] | None = None) -> set[str]:
    acc = acc if acc is not None else set()
    if t[0] == "var":
        acc.add(str(t[1]))
    else:
        collapse_witness_vars(t[1], acc)
        collapse_witness_vars(t[2], acc)
    return acc


def is_collapse_witness(l: Term, r: Term) -> bool:
    """An equation x = T, with x absent from T, collapses every carrier."""
    if l[0] == "var" and l[1] not in collapse_witness_vars(r):
        return True
    if r[0] == "var" and r[1] not in collapse_witness_vars(l):
        return True
    return False


COLLAPSE_CERT_DEPTH = 4
COLLAPSE_CERT_MAX_TERM = 24
COLLAPSE_CERT_MAX_DERIVED = 600


def collapse_cert_vars(t: Term, acc: list[str] | None = None) -> list[str]:
    acc = acc if acc is not None else []
    if t[0] == "var":
        if not str(t[1]).startswith("#") and t[1] not in acc:
            acc.append(t[1])
    else:
        collapse_cert_vars(t[1], acc)
        collapse_cert_vars(t[2], acc)
    return acc


def collapse_cert_size(t: Term) -> int:
    return 1 if t[0] == "var" else 1 + collapse_cert_size(t[1]) + collapse_cert_size(t[2])


def collapse_cert_term(t: Term) -> str:
    if t[0] == "var":
        return str(t[1])
    return f"({collapse_cert_term(t[1])} ◇ {collapse_cert_term(t[2])})"


def collapse_cert_rename(
    eq: tuple[Term, Term],
    prefix: str,
    counter: list[int],
    mapping: dict[str, Term],
) -> tuple[Term, Term]:
    def go(t: Term) -> Term:
        if t[0] == "var":
            name = str(t[1])
            if name.startswith("#"):
                return t
            if name not in mapping:
                mapping[name] = ("var", f"{prefix}{counter[0]}")
                counter[0] += 1
            return mapping[name]
        return ("op", go(t[1]), go(t[2]))

    return go(eq[0]), go(eq[1])


class CollapseCertRule:
    __slots__ = ("name", "vars", "l", "r", "proof_lines", "parents")

    def __init__(
        self,
        name: str,
        vars: list[str],
        l: Term,
        r: Term,
        proof_lines: list[str],
        parents: list[Any] | None = None,
    ) -> None:
        self.name = name
        self.vars = vars
        self.l = l
        self.r = r
        self.proof_lines = proof_lines
        self.parents = list(parents or [])


def collapse_cert_overlap(
    rule_a: CollapseCertRule,
    rule_b: CollapseCertRule,
    fresh: list[int],
) -> list[tuple[Term, Term, dict[str, Term], dict[str, Term], dict[str, Term]]]:
    map_a: dict[str, Term] = {}
    map_b: dict[str, Term] = {}
    lhs_a, rhs_a = collapse_cert_rename((rule_a.l, rule_a.r), f"p{fresh[0]}_", fresh, map_a)
    lhs_b, rhs_b = collapse_cert_rename((rule_b.l, rule_b.r), f"q{fresh[0]}_", fresh, map_b)
    out = []
    for pos, subterm in pc_positions(lhs_a):
        if pos == () or subterm[0] == "var":
            continue
        subst = pc_unify(subterm, lhs_b, {})
        if subst is None:
            continue
        cp_l = pc_apply(pc_replace_at(lhs_a, pos, rhs_b), subst)
        cp_r = pc_apply(rhs_a, subst)
        if cp_l == cp_r:
            continue
        out.append((cp_l, cp_r, map_a, map_b, subst))
    return out


def collapse_cert_subst_unbound(t: Term, bound: set[str], witness: str) -> Term:
    if t[0] == "var":
        name = str(t[1])
        if name.startswith("#"):
            return t
        return t if name in bound else ("var", witness)
    return (
        "op",
        collapse_cert_subst_unbound(t[1], bound, witness),
        collapse_cert_subst_unbound(t[2], bound, witness),
    )


def collapse_cert_emit_rule(
    rule_a: CollapseCertRule,
    rule_b: CollapseCertRule,
    map_a: dict[str, Term],
    map_b: dict[str, Term],
    subst: dict[str, Term],
    cp_l: Term,
    cp_r: Term,
    name: str,
) -> CollapseCertRule:
    vars_out = collapse_cert_vars(cp_l)
    collapse_cert_vars(cp_r, vars_out)
    bound = set(vars_out)
    witness = vars_out[0] if vars_out else "w"

    def argstr(rule: CollapseCertRule, mapping: dict[str, Term]) -> str:
        parts: list[str] = []
        for var in rule.vars:
            if var not in mapping:
                parts.append(witness)
                continue
            arg = pc_apply(mapping[var], subst)
            arg = collapse_cert_subst_unbound(arg, bound, witness)
            parts.append(collapse_cert_term(arg))
        return " ".join(parts)

    proof = [
        f"have _iA := {rule_a.name} {argstr(rule_a, map_a)}".rstrip(),
        f"have _iB := {rule_b.name} {argstr(rule_b, map_b)}".rstrip(),
        "grind",
    ]
    parents = [rule for rule in (rule_a, rule_b) if rule.name != "h"]
    return CollapseCertRule(name, vars_out, cp_l, cp_r, proof, parents=parents)


def collapse_cert_mk_rule(
    rule_a: CollapseCertRule,
    rule_b: CollapseCertRule,
    fresh: list[int],
    name: str,
) -> CollapseCertRule | None:
    best: tuple[int, Term, Term, dict[str, Term], dict[str, Term], dict[str, Term]] | None = None
    for cp_l, cp_r, map_a, map_b, subst in collapse_cert_overlap(rule_a, rule_b, fresh):
        canon_l, canon_r = pc_canon(cp_l, cp_r)
        if not is_collapse_witness(canon_l, canon_r):
            continue
        total_size = collapse_cert_size(cp_l) + collapse_cert_size(cp_r)
        if total_size > COLLAPSE_CERT_MAX_TERM:
            continue
        if best is None or total_size < best[0]:
            best = (total_size, cp_l, cp_r, map_a, map_b, subst)
    if best is None:
        return None
    _, cp_l, cp_r, map_a, map_b, subst = best
    return collapse_cert_emit_rule(rule_a, rule_b, map_a, map_b, subst, cp_l, cp_r, name)


def collapse_cert_path(collapse_rule: CollapseCertRule) -> list[CollapseCertRule]:
    order: list[CollapseCertRule] = []
    visited: set[int] = set()

    def visit(rule: CollapseCertRule) -> None:
        if id(rule) in visited:
            return
        visited.add(id(rule))
        for parent in rule.parents:
            visit(parent)
        order.append(rule)

    visit(collapse_rule)
    remap: dict[str, str] = {}
    idx = 0
    for rule in order:
        if rule is collapse_rule:
            continue
        remap[rule.name] = f"M{idx}"
        idx += 1
    for rule in order:
        if rule.name in remap:
            rule.name = remap[rule.name]
        patched: list[str] = []
        for line in rule.proof_lines:
            for old, new in remap.items():
                line = line.replace(f":= {old} ", f":= {new} ")
            patched.append(line)
        rule.proof_lines = patched
    return order


def collapse_cert_derive(h_rule: CollapseCertRule) -> tuple[list[CollapseCertRule], CollapseCertRule] | None:
    fresh = [0]
    direct = collapse_cert_mk_rule(h_rule, h_rule, fresh, "magic")
    if direct is not None:
        return [direct], direct

    derived = [h_rule]
    seen = {pc_canon(h_rule.l, h_rule.r)}
    frontier = [h_rule]
    lemma_index = 0
    for _depth in range(COLLAPSE_CERT_DEPTH):
        new_frontier: list[CollapseCertRule] = []
        for rule_a in frontier:
            for rule_b in derived:
                for cp_l, cp_r, map_a, map_b, subst in collapse_cert_overlap(rule_a, rule_b, fresh):
                    if collapse_cert_size(cp_l) + collapse_cert_size(cp_r) > COLLAPSE_CERT_MAX_TERM:
                        continue
                    canon_l, canon_r = pc_canon(cp_l, cp_r)
                    if is_collapse_witness(canon_l, canon_r):
                        collapse = collapse_cert_emit_rule(rule_a, rule_b, map_a, map_b, subst, cp_l, cp_r, "magic")
                        return collapse_cert_path(collapse), collapse
                    key = pc_canon(cp_l, cp_r)
                    if key in seen:
                        continue
                    if collapse_cert_size(cp_l) >= collapse_cert_size(cp_r):
                        new_l, new_r = cp_l, cp_r
                    else:
                        new_l, new_r = cp_r, cp_l
                    if new_l[0] == "var":
                        continue
                    seen.add(key)
                    name = f"L{lemma_index}"
                    lemma_index += 1
                    rule = collapse_cert_emit_rule(rule_a, rule_b, map_a, map_b, subst, new_l, new_r, name)
                    derived.append(rule)
                    new_frontier.append(rule)
                    if len(derived) > COLLAPSE_CERT_MAX_DERIVED:
                        return None
        frontier = new_frontier
        if not frontier:
            break
    return None


def collapse_cert_all_subterms(t: Term):
    yield t
    if t[0] == "op":
        yield from collapse_cert_all_subterms(t[1])
        yield from collapse_cert_all_subterms(t[2])


def collapse_cert_match(pat: Term, term: Term, subst: dict[str, Term]) -> dict[str, Term] | None:
    if pat[0] == "var" and not str(pat[1]).startswith("#"):
        name = str(pat[1])
        if name in subst:
            return subst if subst[name] == term else None
        subst = dict(subst)
        subst[name] = term
        return subst
    if pat[0] == "var":
        return subst if term == pat else None
    if term[0] != "op":
        return None
    subst_left = collapse_cert_match(pat[1], term[1], subst)
    if subst_left is None:
        return None
    return collapse_cert_match(pat[2], term[2], subst_left)


def collapse_cert_goal_instance(cp_l: Term, cp_r: Term, all_vars: list[str], goal_l: Term, goal_r: Term) -> str | None:
    if cp_r[0] != "var":
        return None
    for product_side, other_side in ((goal_l, goal_r), (goal_r, goal_l)):
        for subterm in collapse_cert_all_subterms(product_side):
            if subterm[0] != "op":
                continue
            subst = collapse_cert_match(cp_l, subterm, {})
            if subst is None:
                continue
            subst = dict(subst)
            subst.setdefault(str(cp_r[1]), other_side)
            other = collapse_cert_term(other_side)
            args = [collapse_cert_term(subst[var]) if var in subst else other for var in all_vars]
            return " ".join(args)
    return None


def collapse_certificate_body(h_eq: dict[str, Any], g_eq: dict[str, Any]) -> str | None:
    """Prove goals when H derives a carrier-collapse witness."""
    h_lhs, h_rhs = h_eq["lhs"], h_eq["rhs"]
    if is_collapse_witness(h_lhs, h_rhs) and len(h_eq["variables"]) >= 2:
        if h_lhs[0] == "var" and h_lhs[1] not in collapse_witness_vars(h_rhs):
            collapse_var = str(h_lhs[1])
        elif h_rhs[0] == "var" and h_rhs[1] not in collapse_witness_vars(h_lhs):
            collapse_var = str(h_rhs[1])
        else:
            collapse_var = h_eq["variables"][0]

        def direct_args(value: str) -> str:
            return " ".join(value if var == collapse_var else "u" for var in h_eq["variables"])

        goal_vars = list(g_eq["variables"])
        lines = []
        if goal_vars:
            lines.append("intro " + " ".join(goal_vars))
        lines.extend([
            "have triv : ∀ u v : G, u = v := by",
            "  intro u v",
            f"  have hu := h {direct_args('u')}",
            f"  have hv := h {direct_args('v')}",
            "  grind",
            f"exact triv ({collapse_cert_term(g_eq['lhs'])}) ({collapse_cert_term(g_eq['rhs'])})",
        ])
        return "\n".join(lines)
    if h_lhs[0] != "var" and h_rhs[0] != "var":
        return None
    if h_lhs[0] == "var":
        big, lone = h_rhs, h_lhs
    elif h_rhs[0] == "var":
        big, lone = h_lhs, h_rhs
    else:
        return None

    h_rule = CollapseCertRule("h", list(h_eq["variables"]), big, lone, [])
    derived = collapse_cert_derive(h_rule)
    if derived is None:
        return None
    lemmas, collapse = derived

    goal_vars = list(g_eq["variables"])
    goal_l, goal_r = g_eq["lhs"], g_eq["rhs"]
    cp_l, cp_r, all_vars = collapse.l, collapse.r, collapse.vars
    collapse_slot = str(cp_r[1]) if cp_r[0] == "var" else None

    lines: list[str] = []
    if goal_vars:
        lines.append("intro " + " ".join(goal_vars))

    for rule in lemmas:
        binders = " ".join(rule.vars)
        lines.append(f"have {rule.name} : ∀ {binders} : G, {collapse_cert_term(rule.l)} = {collapse_cert_term(rule.r)} := by")
        lines.append("  intro " + binders)
        for proof_line in rule.proof_lines:
            lines.append("  " + proof_line)

    if collapse_slot is not None and collapse_slot in all_vars and goal_vars:
        witness = goal_vars[0]

        def margs(slot_value: str) -> str:
            return " ".join(slot_value if var == collapse_slot else witness for var in all_vars)

        lines.extend([
            "have triv : ∀ u v : G, u = v := by",
            "  intro u v",
            f"  have eu := {collapse.name} {margs('u')}",
            f"  have ev := {collapse.name} {margs('v')}",
            "  grind",
            f"exact triv ({collapse_cert_term(goal_l)}) ({collapse_cert_term(goal_r)})",
        ])
        return "\n".join(lines)

    inst = collapse_cert_goal_instance(cp_l, cp_r, all_vars, goal_l, goal_r)
    if inst is not None:
        lines.append(f"have hgoal := {collapse.name} " + inst)
    lines.append("grind")
    return "\n".join(lines)


def collapse_certificate_bodies(h_eq: dict[str, Any], g_eq: dict[str, Any]):
    body = collapse_certificate_body(h_eq, g_eq)
    if body:
        yield "collapse_certificates", body


def broad_grounding_vars(term: Term, acc: list[str] | None = None) -> list[str]:
    acc = acc if acc is not None else []
    if term[0] == "var":
        if term[1] not in acc:
            acc.append(term[1])
    else:
        broad_grounding_vars(term[1], acc)
        broad_grounding_vars(term[2], acc)
    return acc


def broad_grounding_orientable(lhs: Term, rhs: Term) -> bool:
    left_vars = set(broad_grounding_vars(lhs))
    right_vars = set(broad_grounding_vars(rhs))
    return left_vars <= right_vars or right_vars <= left_vars


def broad_grounding_target_collapse(eq: tuple[Term, Term]) -> bool:
    lhs, rhs = eq
    return is_collapse_witness(lhs, rhs)


def broad_grounding_target_right_irrel(eq: tuple[Term, Term]) -> bool:
    lhs, rhs = eq
    return (
        lhs[0] == "op"
        and rhs[0] == "op"
        and lhs[1] == rhs[1]
        and lhs[2][0] == "var"
        and rhs[2][0] == "var"
        and lhs[2] != rhs[2]
    )


def broad_grounding_target_left_irrel(eq: tuple[Term, Term]) -> bool:
    lhs, rhs = eq
    return (
        lhs[0] == "op"
        and rhs[0] == "op"
        and lhs[2] == rhs[2]
        and lhs[1][0] == "var"
        and rhs[1][0] == "var"
        and lhs[1] != rhs[1]
    )


BROAD_GROUNDING_TARGETS = [
    ("right_irrel", broad_grounding_target_right_irrel),
    ("left_irrel", broad_grounding_target_left_irrel),
    ("collapse", broad_grounding_target_collapse),
]


def self_root_absorption_h(h_eq: dict[str, Any]) -> bool:
    """Detect H shapes like x = x ◇ T or x = T ◇ x."""
    for lone, other in ((h_eq["lhs"], h_eq["rhs"]), (h_eq["rhs"], h_eq["lhs"])):
        if lone[0] == "var" and other[0] == "op" and (other[1] == lone or other[2] == lone):
            return True
    return False


def repeated_self_absorption_h(h_eq: dict[str, Any], g_eq: dict[str, Any] | None = None) -> bool:
    """Detect absorption-like H where a lone variable recurs inside the other side."""
    for lone, other in ((h_eq["lhs"], h_eq["rhs"]), (h_eq["rhs"], h_eq["lhs"])):
        if lone[0] != "var" or other[0] != "op":
            continue
        var = str(lone[1])
        if term_var_count(other, var) < 2:
            continue
        if g_eq is None:
            return True
        goal_pairs = ((g_eq["lhs"], g_eq["rhs"]), (g_eq["rhs"], g_eq["lhs"]))
        if any(side[0] == "var" and side[1] == var and other_side[0] == "op" for side, other_side in goal_pairs):
            return True
    return False


def nested_tail_absorption_h(h_eq: dict[str, Any], g_eq: dict[str, Any] | None = None) -> bool:
    """Detect H like x = (y ◇ (z ◇ x)) ◇ (w ◇ x).

    This family naturally proves `u ◇ (v ◇ u) = u`, then a broad tail
    contraction `((u ◇ v) ◇ v) ◇ (w ◇ t) = t`.
    """
    for lone, other in ((h_eq["lhs"], h_eq["rhs"]), (h_eq["rhs"], h_eq["lhs"])):
        if lone[0] != "var" or other[0] != "op":
            continue
        left, right = other[1], other[2]
        if left[0] != "op" or right[0] != "op":
            continue
        left_tail = left[2]
        if left_tail[0] != "op":
            continue
        if left_tail[2] != lone or right[2] != lone:
            continue
        if left_tail[1] == lone:
            # This is the square-inner subfamily handled cheaply by the
            # generic_right_square_absorption chain.
            continue
        if g_eq is None:
            return True
        goal_pairs = ((g_eq["lhs"], g_eq["rhs"]), (g_eq["rhs"], g_eq["lhs"]))
        if any(side == lone and other_side[0] == "op" for side, other_side in goal_pairs):
            return True
    return False


def broad_grounding_derived_body(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    budget: float = 12.0,
    *,
    full_budget_per_target: bool = False,
) -> tuple[str | None, dict[str, Any]]:
    """Derive a broad grounding helper, then let Lean close the original goal."""
    if not broad_grounding_orientable(h_eq["lhs"], h_eq["rhs"]):
        return None, {
            "kind": "broad_grounding_derived_state",
            "status": "not_applicable",
            "reason": "H is non-orientable; grounding_h is the matching certificate family.",
        }
    attempts: list[dict[str, Any]] = []
    per_target_budget = (
        max(1.0, float(budget))
        if full_budget_per_target
        else max(1.0, float(budget) / max(1, len(BROAD_GROUNDING_TARGETS)))
    )
    for name, predicate in BROAD_GROUNDING_TARGETS:
        tid, recs, meta = pc_saturate(
            [(h_eq["lhs"], h_eq["rhs"])],
            predicate,
            max_rounds=6,
            max_eqs=2000,
            max_size=26,
            time_budget=per_target_budget,
        )
        attempts.append({
            "target_helper": name,
            "status": "derived" if tid is not None else "stuck",
            "generated_equations": len(recs),
            "rounds": meta.get("rounds"),
            "stop_reason": meta.get("stop_reason"),
        })
        if tid is not None:
            body = pc_render(
                tid,
                recs,
                list(g_eq["variables"]),
                goal_lhs=g_eq["lhs"],
                goal_rhs=g_eq["rhs"],
            )
            return body, {
            "kind": "broad_grounding_derived_state",
            "status": "body_built",
            "derived_helper": name,
            "full_budget_per_target": full_budget_per_target,
            "attempts": attempts,
        }
    return None, {
        "kind": "broad_grounding_derived_state",
        "status": "stuck",
        "full_budget_per_target": full_budget_per_target,
        "attempts": attempts,
        "need_hint": "No collapse or factor-irrelevance helper was derived; try goal_superposition, collapse_certificates, or a midpoint close to the best superposition frontier.",
    }


def equation_shape_tags(lhs: Term, rhs: Term) -> list[str]:
    tags: list[str] = []
    for l, r in ((lhs, rhs), (rhs, lhs)):
        if l[0] == "var" and r[0] == "var" and l != r:
            tags.append("const")
        if l[0] == "op" and r[0] == "var":
            if l[1] == r:
                tags.append("proj_l")
            if l[2] == r:
                tags.append("proj_r")
        if l[0] == "op" and r[0] == "op":
            if l[1] == r[1] and l[2] != r[2]:
                tags.append("rowconst")
            if l[2] == r[2] and l[1] != r[1]:
                tags.append("colconst")
            if l[1] != r[1] and l[2] != r[2]:
                tags.append("opconst_like")
            if is_square(l) is not None and is_square(r) is not None and l != r:
                tags.append("square_const")
    return unique(tags)


def target_aux_shape(target_eq: dict[str, Any]) -> str | None:
    lhs, rhs = target_eq["lhs"], target_eq["rhs"]
    tags = equation_shape_tags(lhs, rhs)
    if "const" in tags and lhs[0] == "var" and rhs[0] == "var":
        return "const"
    if "proj_l" in tags:
        return "proj_l"
    if "proj_r" in tags:
        return "proj_r"
    if "rowconst" in tags:
        return "rowconst"
    if "opconst_like" in tags:
        return "opconst"
    if "square_const" in tags:
        return "square_const"
    return None


def superposition_state(
    h_eq: dict[str, Any],
    target_eq: dict[str, Any],
    recs: list[dict[str, Any]],
    meta: dict[str, Any],
    status: str,
    base_names: list[str],
) -> dict[str, Any]:
    goal_l = term_to_str(target_eq["lhs"])
    goal_r = term_to_str(target_eq["rhs"])
    scored: list[dict[str, Any]] = []
    derived_scored: list[dict[str, Any]] = []
    shape_rows: list[dict[str, Any]] = []
    for rid, rec in enumerate(recs[:2000]):
        lhs = term_to_str(rec["lhs"])
        rhs = term_to_str(rec["rhs"])
        text = f"{lhs} = {rhs}"
        score = max(
            difflib.SequenceMatcher(None, lhs, goal_l).ratio(),
            difflib.SequenceMatcher(None, lhs, goal_r).ratio(),
            difflib.SequenceMatcher(None, rhs, goal_l).ratio(),
            difflib.SequenceMatcher(None, rhs, goal_r).ratio(),
            difflib.SequenceMatcher(None, text, target_eq["text"]).ratio(),
        )
        row = {"rid": rid, "similarity": round(score, 3), **pc_rec_summary(rec)}
        scored.append(row)
        if rec.get("deriv") is not None:
            derived_scored.append(row)
            tags = equation_shape_tags(rec["lhs"], rec["rhs"])
            if tags:
                shape_rows.append({**row, "shape_tags": tags})
    scored.sort(key=lambda item: item["similarity"], reverse=True)
    derived_scored.sort(key=lambda item: item["similarity"], reverse=True)
    shape_rows.sort(key=lambda item: (len(item.get("shape_tags", [])), item["similarity"]), reverse=True)
    target_shape = target_aux_shape(target_eq)
    state = {
        "kind": "SuperpositionState",
        "status": status,
        "target": target_eq["text"],
        "target_shape": target_shape,
        "base_names": base_names,
        "generated_equations": len(recs),
        "rounds": meta.get("rounds"),
        "stop_reason": meta.get("stop_reason"),
        "limits": {
            "max_rounds": meta.get("max_rounds"),
            "max_eqs": meta.get("max_eqs"),
            "max_size": meta.get("max_size"),
        },
        "closest_equations": scored[:5],
        "derived_closest_equations": derived_scored[:5],
        "shape_diagnostics": shape_rows[:8],
        "need_hint": {
            "kind": "superposition_subgoal",
            "reason": "proof-carrying superposition did not reach the target; propose a smaller universal midpoint near a closest_equations row",
            "target": target_eq["text"],
            "closest_equation": (derived_scored[0] if derived_scored else scored[0]) if scored else None,
        },
    }
    if target_shape == "rowconst":
        opconst_like = next((row for row in shape_rows if "opconst_like" in row.get("shape_tags", [])), None)
        recommended_next_action = None
        rejected_recommendations: list[dict[str, Any]] = []
        if opconst_like:
            opconst_eq = parse_equation("a ◇ b = c ◇ d")
            opconst_refutation = hint_refutation(h_eq, opconst_eq)
            if opconst_refutation is None:
                recommended_next_action = {
                    "kind": "midpoint",
                    "lemma": "a ◇ b = c ◇ d",
                    "why": "rowconst target is stuck but superposition derived an opconst-like product bridge",
                    "source": opconst_like,
                }
            else:
                rejected_recommendations.append({
                    "kind": "midpoint",
                    "lemma": "a ◇ b = c ◇ d",
                    "status": "refuted_by_small_model",
                    "refutation": opconst_refutation,
                    "source": opconst_like,
                })
        state["rowconst_diagnostics"] = {
            "kind": "rowconst_superposition_diagnostics",
            "best_derived_equations": derived_scored[:5],
            "near_aux_shapes": shape_rows[:8],
            "recommended_next_action": recommended_next_action,
            "rejected_recommendations": rejected_recommendations,
            "secondary_bridge_candidates": [
                "a ◇ b = c ◇ d",
                "a ◇ a = b ◇ b",
                "a ◇ b = a",
                "a ◇ b = b",
            ],
            "reason": "If rowconst itself is hard to prove or insufficient, these derived shapes are useful follow-up bridge candidates.",
        }
        if recommended_next_action:
            state["need_hint"]["recommended_next_action"] = recommended_next_action
    return state


def superposition_prove_detailed(
    h_eq: dict[str, Any],
    target_eq: dict[str, Any],
    assumptions: list[UniversalEquation] | None = None,
    *,
    budget: float = 6.0,
    allow_var_overlap: bool = False,
) -> tuple[str | None, dict[str, Any]]:
    assumptions = assumptions or []
    start = [(h_eq["lhs"], h_eq["rhs"])] + [(a.eq["lhs"], a.eq["rhs"]) for a in assumptions]
    base_names = ["h"] + [a.name for a in assumptions]
    target_sig = pc_canon(target_eq["lhs"], target_eq["rhs"])
    last_state: dict[str, Any] | None = None
    configs = [(3, 360, 14), (4, 650, 16), (5, 900, 20)]
    if budget >= 8.0 or assumptions:
        configs.append((5, 1400, 22))
    if budget >= 12.0:
        configs.append((6, 1800, 24))
    deadline = time.monotonic() + max(1.0, budget)
    for max_rounds, max_eqs, max_size in configs:
        rem = deadline - time.monotonic()
        if rem <= 0.25:
            break
        tid, recs, meta = pc_saturate(
            start,
            lambda eq: pc_canon(eq[0], eq[1]) == target_sig,
            max_rounds=max_rounds,
            max_eqs=max_eqs,
            max_size=max_size,
            time_budget=min(rem, max(0.5, budget / 2)),
            allow_var_overlap=allow_var_overlap,
        )
        if tid is not None:
            body = pc_render(tid, recs, target_eq["variables"], goal_lhs=target_eq["lhs"], goal_rhs=target_eq["rhs"], base_names=base_names)
            return body, superposition_state(h_eq, target_eq, recs, meta, "proved", base_names)
        last_state = superposition_state(h_eq, target_eq, recs, meta, "stuck", base_names)
        if meta.get("stop_reason") == "time_budget":
            break
    return None, last_state or {
        "kind": "SuperpositionState",
        "status": "stuck",
        "target": target_eq["text"],
        "base_names": base_names,
        "generated_equations": 0,
        "need_hint": {"kind": "superposition_subgoal", "reason": "no equations generated before budget expired"},
    }


STANDARD_AUX_EQUATIONS = {
    "const": "a = b",
    "proj_l": "a ◇ b = a",
    "proj_r": "a ◇ b = b",
    "rowconst": "a ◇ b = a ◇ c",
}

SECONDARY_BRIDGE_EQUATIONS = {
    "opconst": "a ◇ b = c ◇ d",
    "square_const": "a ◇ a = b ◇ b",
    "proj_l": "a ◇ b = a",
    "proj_r": "a ◇ b = b",
    "const": "a = b",
    "colconst": "a ◇ b = c ◇ b",
}


def standard_aux_order(call: dict[str, Any] | None = None) -> list[str]:
    raw = []
    if call:
        for key in ("lemmas", "aux", "kinds", "targets"):
            val = call.get(key)
            if isinstance(val, str):
                raw.extend(part.strip() for part in val.split(","))
            elif isinstance(val, list):
                raw.extend(str(part).strip() for part in val)
    if not raw:
        raw = ["const", "proj_l", "proj_r", "rowconst"]
    out: list[str] = []
    for item in raw:
        item = item.lower()
        item = {
            "projection_left": "proj_l",
            "left_projection": "proj_l",
            "projection_right": "proj_r",
            "right_projection": "proj_r",
            "row_constant": "rowconst",
            "row_const": "rowconst",
        }.get(item, item)
        if item in STANDARD_AUX_EQUATIONS and item not in out:
            out.append(item)
    return out


def implied_standard_aux_lemmas(h_eq: dict[str, Any]) -> list[str]:
    """Cheap semantic scout for standard auxiliary lemmas.

    This is deliberately conservative as a scheduler signal, not a soundness
    assumption.  Every returned lemma still has to be proved by the
    proof-carrying superposition engine and accepted by Lean.
    """
    plausible = [
        kind
        for kind in ("const", "proj_l", "proj_r", "rowconst")
        if hint_refutation(h_eq, standard_aux_equation(kind)) is None
    ]
    if "const" in plausible:
        return ["const"]
    return [kind for kind in ("proj_l", "proj_r", "rowconst") if kind in plausible]


def standard_aux_equation(kind: str) -> dict[str, Any]:
    return parse_equation(STANDARD_AUX_EQUATIONS[kind])


def secondary_bridge_order(aux_kind: str) -> list[str]:
    if aux_kind == "rowconst":
        return ["opconst", "square_const", "proj_l", "proj_r", "const"]
    if aux_kind == "proj_l":
        return ["proj_r", "const", "opconst", "square_const"]
    if aux_kind == "proj_r":
        return ["proj_l", "const", "opconst", "square_const"]
    if aux_kind == "const":
        return []
    return ["opconst", "square_const", "proj_l", "proj_r", "const"]


def secondary_bridge_equation(kind: str) -> dict[str, Any]:
    return parse_equation(SECONDARY_BRIDGE_EQUATIONS[kind])


def secondary_bridge_attempt(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    aux: UniversalEquation,
    aux_kind: str,
    deadline: float,
) -> tuple[str | None, dict[str, Any]]:
    attempts: list[dict[str, Any]] = []
    for bridge_kind in secondary_bridge_order(aux_kind):
        if time.monotonic() > deadline - 0.5:
            attempts.append({
                "kind": bridge_kind,
                "status": "skipped_budget_exhausted",
                "equation": SECONDARY_BRIDGE_EQUATIONS[bridge_kind],
            })
            continue
        eq = secondary_bridge_equation(bridge_kind)
        if pc_canon(eq["lhs"], eq["rhs"]) == pc_canon(aux.eq["lhs"], aux.eq["rhs"]):
            continue
        refutation = hint_refutation(h_eq, eq)
        if refutation is not None:
            attempts.append({
                "kind": bridge_kind,
                "status": "refuted_by_small_model",
                "equation": eq["text"],
                "refutation": refutation,
            })
            continue
        bridge = UniversalEquation(name=bridge_kind, eq=eq, extra_args=[])
        proof_body, proof_state = prove_with_assumptions_detailed(h_eq, eq, [aux])
        if proof_body is None:
            attempts.append({
                "kind": bridge_kind,
                "status": "not_proved",
                "equation": eq["text"],
                "proof_state": proof_state,
            })
            continue
        goal_body, goal_state = prove_with_assumptions_detailed(h_eq, g_eq, [aux, bridge])
        attempts.append({
            "kind": bridge_kind,
            "status": "proved" if goal_body else "proved_not_consumed",
            "equation": eq["text"],
            "proof_state": proof_state,
            "consume_state": goal_state,
        })
        if goal_body:
            return "\n".join([
                f"have {bridge_kind} : {lemma_statement(eq)} := by",
                indent(proof_body, 2),
                goal_body,
            ]), {
                "kind": "SecondaryBridgeState",
                "status": "body_built",
                "aux": aux_kind,
                "bridge": bridge_kind,
                "bridge_equation": eq["text"],
                "attempts": attempts,
            }
    need_hint = None
    for attempt in attempts:
        state = attempt.get("consume_state") or attempt.get("proof_state") or {}
        if isinstance(state, dict) and state.get("need_hint"):
            need_hint = state.get("need_hint")
            break
    return None, {
        "kind": "SecondaryBridgeState",
        "status": "stuck",
        "aux": aux_kind,
        "attempts": attempts[:5],
        "need_hint": need_hint or {
            "kind": "secondary_bridge_failed",
            "reason": "A proved auxiliary lemma did not close the goal, and bounded secondary bridges did not close either.",
        },
    }


def standard_aux_tail(kind: str, g_eq: dict[str, Any], h_eq: dict[str, Any], aux: UniversalEquation) -> tuple[str | None, dict[str, Any]]:
    intro = "intro " + " ".join(g_eq["variables"]) if g_eq["variables"] else ""

    def close_with(proof: str, status: str) -> tuple[str, dict[str, Any]]:
        return "\n".join([intro, proof] if intro else [proof]), {
            "kind": "AuxConsumeState",
            "status": status,
            "used_aux": aux.name,
            "need_hint": None,
        }

    if kind == "const":
        lhs = lean_arg(term_to_str(g_eq["lhs"]))
        rhs = lean_arg(term_to_str(g_eq["rhs"]))
        return close_with(f"exact {aux.name} {lhs} {rhs}", "consumed_by_const")

    aux_eq = aux.eq
    exact_line = pc_target_exact_line(
        aux.name,
        aux_eq["lhs"],
        aux_eq["rhs"],
        aux_eq["variables"],
        g_eq["lhs"],
        g_eq["rhs"],
    )
    if exact_line is not None:
        return close_with(exact_line, "consumed_directly")

    hrec = {
        "binders": h_eq["variables"],
        "lhs": h_eq["lhs"],
        "rhs": h_eq["rhs"],
    }
    calc_line = pc_one_h_target_calc(
        hrec,
        aux_eq["lhs"],
        aux_eq["rhs"],
        aux_eq["variables"],
        g_eq["lhs"],
        g_eq["rhs"],
        target_name=aux.name,
    )
    if calc_line is not None:
        return close_with(calc_line, "consumed_by_one_h_aux")

    calc_line = pc_path_target_calc(
        hrec,
        aux_eq["lhs"],
        aux_eq["rhs"],
        aux_eq["variables"],
        g_eq["lhs"],
        g_eq["rhs"],
        target_name=aux.name,
    )
    if calc_line is not None:
        return close_with(calc_line, "consumed_by_h_aux_path")

    goal_body, goal_state = prove_with_assumptions_detailed(h_eq, g_eq, [aux])
    return goal_body, goal_state


def standard_aux_superposition_attempt(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    call: dict[str, Any] | None = None,
) -> tuple[str | None, dict[str, Any]]:
    call = call or {}
    kinds = standard_aux_order(call)
    implied_kinds = implied_standard_aux_lemmas(h_eq)
    prefer_implied = call.get("prefer_implied", True) is not False
    if prefer_implied and implied_kinds:
        preferred = [kind for kind in implied_kinds if kind in kinds]
        remainder = [kind for kind in kinds if kind not in preferred]
        kinds = preferred + remainder
    total_budget = float(call.get("budget") or call.get("time_budget") or 10.0)
    deadline = time.monotonic() + max(1.0, total_budget)
    allow_overlap_fallback = bool(call.get("allow_var_overlap", True))
    attempts: list[dict[str, Any]] = []
    for idx, kind in enumerate(kinds):
        rem = deadline - time.monotonic()
        if rem <= 0.25:
            attempts.append({
                "kind": kind,
                "status": "skipped_budget_exhausted",
                "equation": STANDARD_AUX_EQUATIONS[kind],
            })
            continue
        eq = standard_aux_equation(kind)
        refutation = hint_refutation(h_eq, eq)
        if refutation is not None:
            attempts.append({
                "kind": kind,
                "status": "refuted_by_small_model",
                "equation": eq["text"],
                "refutation": refutation,
            })
            continue
        remaining = max(1, len(kinds) - idx)
        focused_floor = 1.0
        if kind in implied_kinds:
            focused_floor = 8.0 if kind in {"proj_l", "proj_r"} else 5.0
        attempt_budget = min(rem, max(1.0, rem / remaining, focused_floor))
        proof_body, proof_state = superposition_prove_detailed(
            h_eq,
            eq,
            budget=attempt_budget,
            allow_var_overlap=False,
        )
        if proof_body is None and allow_overlap_fallback:
            overlap_rem = deadline - time.monotonic()
            if overlap_rem > 0.75:
                overlap_body, overlap_state = superposition_prove_detailed(
                    h_eq,
                    eq,
                    budget=min(overlap_rem, max(1.0, attempt_budget * 0.5)),
                    allow_var_overlap=True,
                )
                if isinstance(proof_state, dict):
                    proof_state = dict(proof_state)
                    proof_state["overlap_fallback_state"] = overlap_state
                else:
                    proof_state = {"overlap_fallback_state": overlap_state}
                if overlap_body is not None:
                    proof_body = overlap_body
                    proof_state["used_overlap_fallback"] = True
        if proof_body is None:
            budget_starved = isinstance(proof_state, dict) and (
                proof_state.get("stop_reason") == "time_budget"
                or (
                    isinstance(proof_state.get("superposition_state"), dict)
                    and proof_state["superposition_state"].get("stop_reason") == "time_budget"
                )
                or (
                    isinstance(proof_state.get("overlap_fallback_state"), dict)
                    and proof_state["overlap_fallback_state"].get("stop_reason") == "time_budget"
                )
            )
            attempts.append({
                "kind": kind,
                "status": "budget_starved" if budget_starved else "not_proved",
                "equation": eq["text"],
                "attempt_budget": round(attempt_budget, 3),
                "implied_by_scout": kind in implied_kinds,
                "proof_state": proof_state,
            })
            continue
        aux = UniversalEquation(name=kind, eq=eq, extra_args=[])
        tail, consume_state = standard_aux_tail(kind, g_eq, h_eq, aux)
        secondary_tail = None
        secondary_state = None
        if tail is None:
            secondary_tail, secondary_state = secondary_bridge_attempt(h_eq, g_eq, aux, kind, deadline)
        attempts.append({
            "kind": kind,
            "status": "proved" if (tail or secondary_tail) else "proved_not_consumed",
            "equation": eq["text"],
            "attempt_budget": round(attempt_budget, 3),
            "implied_by_scout": kind in implied_kinds,
            "proof_state": proof_state,
            "consume_state": consume_state,
            "secondary_state": secondary_state,
        })
        if tail or secondary_tail:
            body = "\n".join([
                f"have {kind} : {lemma_statement(eq)} := by",
                indent(proof_body, 2),
                tail or secondary_tail or "",
            ])
            return body, {
                "kind": "StandardAuxSuperpositionState",
                "status": "body_built",
                "used_aux": kind,
                "implied_aux": implied_kinds,
                "used_secondary_bridge": secondary_state.get("bridge") if isinstance(secondary_state, dict) else None,
                "attempts": attempts,
            }
    need_hint = None
    for attempt in attempts:
        states = []
        if attempt.get("status") == "proved_not_consumed":
            states = [attempt.get("secondary_state"), attempt.get("consume_state"), attempt.get("proof_state")]
        else:
            states = [attempt.get("proof_state"), attempt.get("consume_state")]
        for state in states:
            if isinstance(state, dict) and state.get("need_hint"):
                if attempt.get("status") == "proved_not_consumed":
                    need_hint = {
                        "kind": "standard_aux_followup",
                        "proved_aux": attempt.get("kind"),
                        "proved_aux_equation": attempt.get("equation"),
                        "reason": "The auxiliary lemma was proved from H, but the goal did not close with current bounded consumers.",
                        "next": state.get("need_hint"),
                    }
                else:
                    need_hint = state.get("need_hint")
                break
        if need_hint is not None:
            break
    return None, {
        "kind": "StandardAuxSuperpositionState",
        "status": "stuck",
        "attempted_aux": kinds,
        "implied_aux": implied_kinds,
        "attempts": attempts[:5],
        "need_hint": need_hint or {
            "kind": "standard_aux_failed",
            "reason": "No standard auxiliary lemma was both proved from H and useful for the goal.",
            "next_action": "Propose a custom midpoint/lemma_chain or try a different tool.",
        },
    }


def native_deep_true_candidates(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    budget: float,
):
    """Late native portfolio covering every retired true-side mechanism class."""
    deadline = time.monotonic() + max(1.0, budget)

    for route, body in collapse_certificate_bodies(h_eq, g_eq):
        if time.monotonic() >= deadline:
            return
        yield route, body, {"family": "collapse_certificates"}

    for route, body in grounding_h_certificate_bodies(h_eq, g_eq):
        if time.monotonic() >= deadline:
            return
        yield route, body, {"family": "grounding_h"}

    remaining = deadline - time.monotonic()
    if remaining > 1.0:
        body, state = broad_grounding_derived_body(
            h_eq,
            g_eq,
            budget=min(12.0, max(1.0, remaining * 0.45)),
        )
        if body:
            yield "broad_grounding_derived", body, state

    remaining = deadline - time.monotonic()
    if remaining > 1.0:
        body, state = standard_aux_superposition_attempt(
            h_eq,
            g_eq,
            {
                "lemmas": ["const", "proj_l", "proj_r", "rowconst"],
                "budget": min(12.0, max(1.0, remaining * 0.35)),
            },
        )
        if body:
            yield "standard_aux_superposition", body, state

    for route, body in native_saturation_bodies(h_eq, g_eq):
        if time.monotonic() >= deadline:
            return
        yield route, body, {"family": "deep_saturation"}

    remaining = deadline - time.monotonic()
    if remaining > 1.0:
        body, state = superposition_prove_detailed(
            h_eq,
            g_eq,
            budget=min(12.0, max(1.0, remaining)),
            allow_var_overlap=True,
        )
        if body:
            yield "goal_superposition:overlap", body, state


def prove_with_assumptions_detailed(
    h_eq: dict[str, Any],
    target_eq: dict[str, Any],
    assumptions: list[UniversalEquation] | None = None,
    *,
    extra_h_args: list[tuple[str, ...]] | None = None,
    superposition_budget: float = 5.0,
) -> tuple[str | None, dict[str, Any]]:
    last_state: dict[str, Any] | None = None
    tiers = [
        (48, 96, 0),
        (64, 128, 600),
        (80, 180, 1600),
    ]
    if assumptions:
        tiers.append((140, 320, 4000))
    for h_limit, lemma_limit, congruence_cap in tiers:
        body = h_graph_body(
            h_eq,
            target_eq,
            h_limit,
            lemmas=[assumption.as_lemma() for assumption in assumptions or []],
            lemma_limit=lemma_limit,
            congruence_cap=congruence_cap,
            extra_args=extra_h_args,
        )
        state = graph_search_state(
            h_eq,
            target_eq,
            assumptions,
            h_limit=h_limit,
            lemma_limit=lemma_limit,
            congruence_cap=congruence_cap,
            extra_args=extra_h_args,
            status="proved" if body else "stuck",
        )
        if body:
            return body, state
        last_state = state
    pc_body, pc_state = superposition_prove_detailed(
        h_eq,
        target_eq,
        assumptions,
        budget=superposition_budget,
    )
    if pc_body is None and (assumptions or target_aux_shape(target_eq)):
        overlap_budget = max(1.0, min(3.0, superposition_budget / 3.0))
        pc_body, pc_state = superposition_prove_detailed(
            h_eq,
            target_eq,
            assumptions,
            budget=overlap_budget,
            allow_var_overlap=True,
        )
    if pc_body:
        return pc_body, pc_state
    if last_state is not None:
        last_state = dict(last_state)
        last_state["superposition_state"] = pc_state
        last_state["need_hint"] = pc_state.get("need_hint") or last_state.get("need_hint")
        return None, last_state
    return None, last_state or {
        "kind": "SearchState",
        "status": "stuck",
        "target": target_eq["text"],
    }


def prove_with_assumptions(
    h_eq: dict[str, Any],
    target_eq: dict[str, Any],
    assumptions: list[UniversalEquation] | None = None,
) -> str | None:
    body, _state = prove_with_assumptions_detailed(h_eq, target_eq, assumptions)
    return body


def midpoint_progress_signal(state: dict[str, Any] | None) -> float:
    """Extract a deliberately coarse, replaceable progress signal."""
    source = state if isinstance(state, dict) else {}
    score = 0.0
    if source.get("closest_pairs"):
        score += 0.20
    if source.get("suggested_next_actions") or source.get("need_hint"):
        score += 0.10
    superposition = source.get("superposition_state")
    if isinstance(superposition, dict):
        if superposition.get("derived_closest_equations"):
            score += 0.35
        if superposition.get("shape_diagnostics"):
            score += 0.20
        if superposition.get("stop_reason") not in {None, "time_budget"}:
            score += 0.05
    return min(1.0, score)


def generic_midpoint_chain_attempt(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    hints: list[UniversalEquation],
    *,
    budget_policy: dict[str, Any] | MidpointBudgetPolicy | None = None,
    total_budget: float | None = None,
) -> tuple[str | None, dict[str, Any]]:
    limited_hints = hints[:5]
    policy = (
        budget_policy
        if isinstance(budget_policy, MidpointBudgetPolicy)
        else MidpointBudgetPolicy.from_mapping(
            budget_policy,
            candidate_count=len(limited_hints),
            requested_total=total_budget,
        )
    )
    broker = RenewableBudgetBroker(policy)
    proof_lines: list[str] = []
    proved: list[UniversalEquation] = []
    proved_indices: set[int] = set()
    failed: list[dict[str, Any]] = []
    candidates: dict[int, dict[str, Any]] = {}

    for index, hint in enumerate(limited_hints):
        same_as_goal = (
            (hint.eq["lhs"] == g_eq["lhs"] and hint.eq["rhs"] == g_eq["rhs"])
            or (hint.eq["lhs"] == g_eq["rhs"] and hint.eq["rhs"] == g_eq["lhs"])
        )
        if same_as_goal:
            failed.append({
                "stage": "goal_as_midpoint",
                "name": hint.name,
                "equation": hint.eq["text"],
                "failure": {
                    "reason": "The proposed midpoint is the goal itself, so it does not split H=>G into easier subgoals.",
                    "repair": "Return a smaller reusable helper equation or a false_model_search route instead.",
                },
            })
            continue
        refutation = hint_refutation(h_eq, hint.eq)
        if refutation is not None:
            failed.append({
                "stage": "plausibility_filter",
                "name": hint.name,
                "equation": hint.eq["text"],
                "failure": refutation,
            })
            continue

        relevance = min(1.0, max(0.0, float(-hint_score(hint, g_eq)[0])) / 24.0)
        reusable = 1.0 if helper_kind(hint.eq["text"]) else 0.0
        common_score = policy.relevance_weight * relevance + policy.reuse_weight * reusable
        candidates[index] = {
            "index": index,
            "hint": hint,
            "relevance": relevance,
            "reusable": reusable,
            "proof_body": None,
            "proof_state": None,
            "consume_body": None,
            "consume_state": None,
        }
        metadata = {
            "candidate_index": index,
            "candidate": hint.name,
            "equation": hint.eq["text"],
        }
        broker.register(
            f"candidate:{index}:consume",
            base_score=policy.consume_priority + common_score,
            metadata={**metadata, "leg": "consume"},
        )
        broker.register(
            f"candidate:{index}:attain",
            base_score=policy.attain_priority + common_score,
            metadata={**metadata, "leg": "attain"},
        )

    broker.register(
        "root:consume",
        base_score=policy.goal_priority,
        metadata={"candidate": "root", "leg": "consume_proved_set"},
        enabled=False,
    )

    solution_body: str | None = None
    last_goal_state: dict[str, Any] | None = None
    while solution_body is None:
        lease = broker.next_grant()
        if lease is None:
            break
        task, grant = lease
        started = time.monotonic()
        leg = task.metadata.get("leg")
        index = task.metadata.get("candidate_index")
        candidate = candidates.get(index) if isinstance(index, int) else None
        body: str | None = None
        state: dict[str, Any] = {}

        if leg == "attain" and candidate is not None:
            hint = candidate["hint"]
            body, state = prove_with_assumptions_detailed(
                h_eq,
                hint.eq,
                list(proved),
                extra_h_args=hint.proof_extra_args(),
                superposition_budget=grant,
            )
            candidate["proof_state"] = state
            if body is not None and index not in proved_indices:
                candidate["proof_body"] = body
                proof_lines.append(
                    f"have {hint.name} : {lemma_statement(hint.eq)} := by\n"
                    f"{indent(body, 2)}"
                )
                proved.append(hint)
                proved_indices.add(index)
                broker.report(
                    task.task_id,
                    "succeeded",
                    progress=1.0,
                    elapsed_seconds=time.monotonic() - started,
                    detail={"proved_lemma": hint.name},
                )
                broker.advance_context()
                broker.update("root:consume", enabled=True)
                broker.update(f"candidate:{index}:consume", companion_succeeded=True)
                if candidate.get("consume_body"):
                    solution_body = "\n".join([*proof_lines, candidate["consume_body"]])
                continue
        elif leg == "consume" and candidate is not None:
            hint = candidate["hint"]
            assumptions = list(proved)
            if index not in proved_indices:
                assumptions.append(hint)
            body, state = prove_with_assumptions_detailed(
                h_eq,
                g_eq,
                assumptions,
                superposition_budget=grant,
            )
            candidate["consume_state"] = state
            last_goal_state = state
            if body is not None:
                candidate["consume_body"] = body
                broker.report(
                    task.task_id,
                    "succeeded",
                    progress=1.0,
                    elapsed_seconds=time.monotonic() - started,
                    detail={"candidate_is_attained": index in proved_indices},
                )
                broker.update(f"candidate:{index}:attain", companion_succeeded=True)
                if index in proved_indices:
                    solution_body = "\n".join([*proof_lines, body])
                continue
        elif leg == "consume_proved_set" and proved:
            body, state = prove_with_assumptions_detailed(
                h_eq,
                g_eq,
                list(proved),
                superposition_budget=grant,
            )
            last_goal_state = state
            if body is not None:
                broker.report(
                    task.task_id,
                    "succeeded",
                    progress=1.0,
                    elapsed_seconds=time.monotonic() - started,
                    detail={"proved_lemma_count": len(proved)},
                )
                solution_body = "\n".join([*proof_lines, body])
                continue
        else:
            state = {
                "kind": "BudgetTaskState",
                "status": "not_runnable",
                "leg": leg,
            }

        broker.report(
            task.task_id,
            "retryable",
            progress=midpoint_progress_signal(state),
            elapsed_seconds=time.monotonic() - started,
            detail={
                "search_status": state.get("status"),
                "stop_reason": (state.get("superposition_state") or {}).get("stop_reason")
                if isinstance(state.get("superposition_state"), dict)
                else None,
            },
        )

    for index, candidate in candidates.items():
        if index in proved_indices:
            continue
        hint = candidate["hint"]
        failed.append({
            "stage": "prove_midpoint",
            "name": hint.name,
            "equation": hint.eq["text"],
            "search_state": candidate.get("proof_state") or {
                "kind": "SearchState",
                "status": "not_started_before_budget_exhausted",
            },
        })

    summary: dict[str, Any] = {
        "protocol_version": PROTOCOL_VERSION,
        "kind": "midpoint_chain_attempt",
        "status": "stuck",
        "source": "generic_midpoint_chain",
        "proposed_lemmas": [
            {
                "name": hint.name,
                "equation": hint.eq["text"],
                "score": -hint_score(hint, g_eq)[0],
            }
            for hint in limited_hints
        ],
        "proved_lemmas": [
            {"name": hint.name, "equation": hint.eq["text"]} for hint in proved
        ],
        "failed_midpoints": failed[:3],
        "budget_allocation": broker.snapshot(),
    }
    if not hints:
        summary["status"] = "no_parseable_midpoints"
        summary["need_hint"] = {
            "kind": "midpoint",
            "reason": "return one small universal equation, e.g. a ◇ b = b",
        }
        summary["suggested_next_actions"] = [{
            "kind": "midpoint",
            "lemma": "a ◇ b = b",
            "why": "example shape only; replace with a problem-specific bridge",
        }]
        return None, summary
    if not proved:
        summary["status"] = "no_midpoint_proved"
        bridge_failures = [item for item in failed if "search_state" in item]
        goal_as_midpoint_failures = [item for item in failed if item.get("stage") == "goal_as_midpoint"]
        if goal_as_midpoint_failures:
            summary["need_hint"] = {
                "kind": "replace_goal_as_midpoint",
                "reason": "The proposed midpoint repeated the target goal and did not reduce the proof obligation.",
                "bad_midpoint": goal_as_midpoint_failures[0].get("equation"),
                "next_action": "Propose a smaller universal midpoint/lemma_chain that would imply the goal, or switch to a concrete false_model_search route.",
            }
        elif bridge_failures:
            summary["need_hint"] = bridge_failures[0]["search_state"].get("need_hint")
        elif failed:
            summary["need_hint"] = {
                "kind": "replace_midpoint",
                "reason": "proposed midpoint was refuted by a small model of H",
            }
        if summary.get("need_hint"):
            summary["suggested_next_actions"] = [summary["need_hint"]]
        return None, summary
    if solution_body is None:
        summary["status"] = "proved_midpoints_not_consumed"
        goal_state = last_goal_state or {
            "kind": "SearchState",
            "status": "budget_exhausted",
            "need_hint": "The shared midpoint budget was exhausted before a proved helper set closed the goal.",
        }
        summary["goal_search_state"] = goal_state
        summary["need_hint"] = goal_state.get("need_hint")
        if goal_state.get("suggested_next_actions"):
            summary["suggested_next_actions"] = goal_state.get("suggested_next_actions")
        return None, summary
    summary["status"] = "body_built"
    summary["goal_search_state"] = last_goal_state
    return solution_body, summary


def generic_midpoint_chain_body(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    hints: list[UniversalEquation],
) -> str | None:
    """Prove LLM-proposed lemmas in order, then use the proved assumptions."""
    body, _state = generic_midpoint_chain_attempt(h_eq, g_eq, hints)
    return body


def hint_payload_attempt(
    payload: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    *,
    capability_mask: Any = None,
) -> tuple[str | None, dict[str, Any]]:
    hints = ordered_hints_for_payload(payload, parse_universal_equations(payload), g_eq)
    body, state = generic_midpoint_chain_attempt(
        h_eq,
        g_eq,
        hints,
        budget_policy=payload.get("budget_policy"),
        total_budget=payload.get("budget") or payload.get("time_budget"),
    )
    if body:
        return body, state
    kinds = {helper_kind(hint.eq["text"]) for hint in hints}
    focused_fallbacks_withheld: list[str] = []
    right_square_gate = capability_gate_state("right_square_chain", capability_mask)
    if {"square_absorb", "right_square"} <= kinds and right_square_gate is None:
        body = generic_right_square_chain_body(h_eq, g_eq)
        if body:
            state["status"] = "body_built_by_focused_right_square_fallback"
            return body, state
    elif {"square_absorb", "right_square"} <= kinds:
        focused_fallbacks_withheld.append("tool:right_square_chain")
    square_sandwich_gate = capability_gate_state("square_sandwich_chain", capability_mask)
    if {"square_const", "right_id_square", "sandwich"} <= kinds and square_sandwich_gate is None:
        body = square_sandwich_chain_body(h_eq, g_eq)
        if body:
            state["status"] = "body_built_by_focused_square_sandwich_fallback"
            return body, state
    elif {"square_const", "right_id_square", "sandwich"} <= kinds:
        focused_fallbacks_withheld.append("tool:square_sandwich_chain")
    if focused_fallbacks_withheld:
        state["focused_fallbacks_withheld"] = focused_fallbacks_withheld
    return None, state


def body_from_hint_payload(
    payload: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    *,
    capability_mask: Any = None,
) -> str | None:
    body, _state = hint_payload_attempt(payload, h_eq, g_eq, capability_mask=capability_mask)
    return body


# Focused true-side tools


def op(left: Term, right: Term) -> Term:
    return ("op", left, right)


def sq(t: Term) -> Term:
    return ("op", t, t)


def is_square(t: Term):
    return t[1] if t[0] == "op" and t[1] == t[2] else None


def special_right_square_h(h_eq: dict[str, Any]):
    lhs, rhs = h_eq["lhs"], h_eq["rhs"]
    if lhs[0] != "var" or rhs[0] != "op":
        return None
    x = lhs[1]
    if rhs[2] != sq(("var", x)):
        return None
    left = rhs[1]
    if left[0] != "op" or left[1][0] != "var" or left[2][0] != "op":
        return None
    y = left[1][1]
    yz = left[2]
    if yz[1] != ("var", y) or yz[2][0] != "var":
        return None
    z = yz[2][1]
    return (x, y, z) if len({x, y, z}) == 3 else None


def right_square_goal(g_eq: dict[str, Any]):
    lhs, rhs = g_eq["lhs"], g_eq["rhs"]
    if lhs[0] != "var" or rhs[0] != "op" or rhs[1] != lhs:
        return None
    inner = rhs[2]
    if inner[0] != "op" or inner[2] != lhs or inner[1][0] != "op":
        return None
    b = inner[1][1]
    if inner[1][2] != op(lhs, b):
        return None
    return term_to_str(lhs), term_to_str(b)


def right_square_helper_lines(h_eq: dict[str, Any]) -> list[str] | None:
    m = special_right_square_h(h_eq)
    if m is None:
        return None
    hx, hy, hz = m

    def h_call(x: str, y: str, z: str) -> str:
        mp = {hx: x, hy: y, hz: z}
        return "h " + " ".join(lean_arg(mp[v]) for v in h_eq["variables"])

    return [
        "have E4 : ∀ (v0 v1 v2 v3 v4 : G), ((v0 ◇ (v0 ◇ v1)) ◇ ((v2 ◇ (v2 ◇ v3)) ◇ ((v4 ◇ v4) ◇ (v4 ◇ v4)))) = v4 := by",
        "  intro v0 v1 v2 v3 v4",
        f"  have ia : v4 = ((v0 ◇ (v0 ◇ v1)) ◇ (v4 ◇ v4)) := {h_call('v4', 'v0', 'v1')}",
        f"  have ib : (v4 ◇ v4) = ((v2 ◇ (v2 ◇ v3)) ◇ ((v4 ◇ v4) ◇ (v4 ◇ v4))) := {h_call('(v4 ◇ v4)', 'v2', 'v3')}",
        "  have ic : ((v0 ◇ (v0 ◇ v1)) ◇ (v4 ◇ v4)) = ((v0 ◇ (v0 ◇ v1)) ◇ ((v2 ◇ (v2 ◇ v3)) ◇ ((v4 ◇ v4) ◇ (v4 ◇ v4)))) := congrArg (fun t => ((v0 ◇ (v0 ◇ v1)) ◇ t)) ib",
        "  exact (ia.trans ic).symm",
        "have raw_square_absorb : ∀ (v0 v1 v2 v3 : G), (v0 ◇ (v1 ◇ v1)) = v1 := by",
        "  intro v0 v1 v2 v3",
        f"  have ia : v1 = (((v2 ◇ (v2 ◇ v3)) ◇ ((v2 ◇ (v2 ◇ v3)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0)))) ◇ (v1 ◇ v1)) := {h_call('v1', '(v2 ◇ (v2 ◇ v3))', '((v0 ◇ v0) ◇ (v0 ◇ v0))')}",
        "  have ib : ((v2 ◇ (v2 ◇ v3)) ◇ ((v2 ◇ (v2 ◇ v3)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0)))) = v0 := E4 v2 v3 v2 v3 v0",
        "  have ic : (((v2 ◇ (v2 ◇ v3)) ◇ ((v2 ◇ (v2 ◇ v3)) ◇ ((v0 ◇ v0) ◇ (v0 ◇ v0)))) ◇ (v1 ◇ v1)) = (v0 ◇ (v1 ◇ v1)) := congrArg (fun t => t ◇ (v1 ◇ v1)) ib",
        "  exact (ia.trans ic).symm",
        "have square_absorb : ∀ (v0 v1 : G), (v0 ◇ (v1 ◇ v1)) = v1 := by",
        "  intro v0 v1",
        "  exact raw_square_absorb v0 v1 v0 v0",
        "have raw_right_square : ∀ (v0 v1 v2 v3 v4 v5 : G), (v0 ◇ v1) = (v1 ◇ v1) := by",
        "  intro v0 v1 v2 v3 v4 v5",
        "  have ia : v0 ◇ ((v1 ◇ v1) ◇ (v1 ◇ v1)) = (v1 ◇ v1) := square_absorb v0 (v1 ◇ v1)",
        "  have ib : ((v1 ◇ v1) ◇ (v1 ◇ v1)) = v1 := square_absorb (v1 ◇ v1) v1",
        "  have ic : v0 ◇ ((v1 ◇ v1) ◇ (v1 ◇ v1)) = v0 ◇ v1 := congrArg (fun t => v0 ◇ t) ib",
        "  exact ic.symm.trans ia",
        "have right_square : ∀ (v0 v1 : G), (v0 ◇ v1) = (v1 ◇ v1) := by",
        "  intro v0 v1",
        "  exact raw_right_square v0 v1 v0 v0 v0 v0",
    ]


def right_square_chain_body(h_eq: dict[str, Any], g_eq: dict[str, Any]) -> str | None:
    helper = right_square_helper_lines(h_eq)
    goal = right_square_goal(g_eq)
    if helper is None or goal is None:
        return None
    x, y = goal
    xy = f"({x} ◇ {y})"
    yxy = f"({y} ◇ {xy})"
    inner = f"({yxy} ◇ {x})"
    lines = ["intro " + " ".join(g_eq["variables"])] + helper + [
        f"have t1 : {yxy} = ({xy} ◇ {xy}) := right_square {y} {xy}",
        f"have t2 : {inner} = ({x} ◇ {x}) := by",
        f"  have a : {inner} = (({xy} ◇ {xy}) ◇ {x}) := congrArg (fun t => t ◇ {x}) t1",
        f"  have b : (({xy} ◇ {xy}) ◇ {x}) = ({x} ◇ {x}) := right_square ({xy} ◇ {xy}) {x}",
        "  exact a.trans b",
        f"have t3 : {x} ◇ {inner} = {x} ◇ ({x} ◇ {x}) := congrArg (fun u => {x} ◇ u) t2",
        f"have t4 : {x} ◇ ({x} ◇ {x}) = {x} := square_absorb {x} {x}",
        "exact (t3.trans t4).symm",
    ]
    return "\n".join(lines)


def generic_right_square_chain_body(h_eq: dict[str, Any], g_eq: dict[str, Any]) -> str | None:
    helper = right_square_helper_lines(h_eq)
    if helper is None:
        return None
    lemmas = [
        {"name": "square_absorb", "eq": parse_equation("u ◇ (v ◇ v) = v")},
        {"name": "right_square", "eq": parse_equation("u ◇ v = v ◇ v")},
    ]
    goal_body = h_graph_body(h_eq, g_eq, 64, lemmas=lemmas, lemma_limit=160, congruence_cap=1600)
    if goal_body is None:
        return None
    parts = goal_body.splitlines()
    if parts and parts[0].startswith("intro "):
        return "\n".join([parts[0], *helper, *parts[1:]])
    return "\n".join(helper + [goal_body])


def square_sandwich_h(h_eq: dict[str, Any]):
    lhs, rhs = h_eq["lhs"], h_eq["rhs"]
    if lhs[0] != "var" or rhs[0] != "op":
        return None
    x = lhs[1]
    left, square = rhs[1], rhs[2]
    if left[0] != "op" or square[0] != "op":
        return None
    yx, y2 = left[1], left[2]
    if yx[0] != "op" or yx[1][0] != "var" or yx[2] != ("var", x) or y2[0] != "var":
        return None
    y = yx[1][1]
    if y2[1] != y or square[1][0] != "var" or square[2] != square[1]:
        return None
    z = square[1][1]
    return (x, y, z) if len({x, y, z}) == 3 else None


def square_sandwich_helper_lines(h_eq: dict[str, Any], g_eq: dict[str, Any]) -> list[str] | None:
    m = square_sandwich_h(h_eq)
    if m is None or not g_eq["variables"]:
        return None
    hx, hy, hz = m

    def h_call(x: str, y: str, z: str) -> str:
        mp = {hx: x, hy: y, hz: z}
        return "h " + " ".join(lean_arg(mp[v]) for v in h_eq["variables"])

    return [
        "intro " + " ".join(g_eq["variables"]),
        "have square_const : ∀ v w : G, v ◇ v = w ◇ w := by",
        "  intro v w",
        "  let A : G := (v ◇ (v ◇ v)) ◇ v",
        "  have hvA : v ◇ v = A ◇ (v ◇ v) := by",
        f"    simpa [A] using {h_call('v ◇ v', 'v', 'v')}",
        "  have hwA : v ◇ v = A ◇ (w ◇ w) := by",
        f"    simpa [A] using {h_call('v ◇ v', 'v', 'w')}",
        "  have ev : v ◇ v = ((v ◇ v) ◇ A) ◇ (v ◇ v) := by",
        "    calc",
        f"      v ◇ v = ((A ◇ (v ◇ v)) ◇ A) ◇ (v ◇ v) := {h_call('v ◇ v', 'A', 'v')}",
        "      _ = ((v ◇ v) ◇ A) ◇ (v ◇ v) := by rw [← hvA]",
        "  have ew : w ◇ w = ((v ◇ v) ◇ A) ◇ (v ◇ v) := by",
        "    calc",
        f"      w ◇ w = ((A ◇ (w ◇ w)) ◇ A) ◇ (v ◇ v) := {h_call('w ◇ w', 'A', 'v')}",
        "      _ = ((v ◇ v) ◇ A) ◇ (v ◇ v) := by rw [← hwA]",
        "  exact ev.trans ew.symm",
        "have right_id_square : ∀ a b : G, a ◇ (b ◇ b) = a := by",
        "  intro a b",
        "  have sqv : a ◇ a = b ◇ b := square_const a b",
        "  have step1 : ((b ◇ b) ◇ a) ◇ (b ◇ b) = a := by",
        "    calc",
        "      ((b ◇ b) ◇ a) ◇ (b ◇ b) = ((a ◇ a) ◇ a) ◇ (b ◇ b) := by rw [← sqv]",
        f"      _ = a := ({h_call('a', 'a', 'b')}).symm",
        "  have step2 : a = a ◇ (b ◇ b) := by",
        "    calc",
        f"      a = (((b ◇ b) ◇ a) ◇ (b ◇ b)) ◇ (b ◇ b) := {h_call('a', 'b ◇ b', 'b')}",
        "      _ = a ◇ (b ◇ b) := by rw [step1]",
        "  exact step2.symm",
        "have sandwich : ∀ a b : G, (b ◇ a) ◇ b = a := by",
        "  intro a b",
        "  calc",
        "    (b ◇ a) ◇ b = ((b ◇ a) ◇ b) ◇ (a ◇ a) := (right_id_square ((b ◇ a) ◇ b) a).symm",
        f"    _ = a := ({h_call('a', 'b', 'a')}).symm",
        "have left_sandwich : ∀ a b : G, b ◇ (a ◇ b) = a := by",
        "  intro a b",
        "  have d_eq_a : (((a ◇ b) ◇ a) ◇ (a ◇ b)) = a := by",
        "    calc",
        "      (((a ◇ b) ◇ a) ◇ (a ◇ b)) = (((a ◇ b) ◇ a) ◇ (a ◇ b)) ◇ (a ◇ a) := (right_id_square (((a ◇ b) ◇ a) ◇ (a ◇ b)) a).symm",
        f"      _ = a := ({h_call('a', 'a ◇ b', 'a')}).symm",
        "  calc",
        "    b ◇ (a ◇ b) = (((a ◇ b) ◇ a) ◇ (a ◇ b)) := congrArg (fun u => u ◇ (a ◇ b)) (sandwich b a).symm",
        "    _ = a := d_eq_a",
    ]


class SquareReducer:
    def __init__(self, witness: str):
        self.witness_var = witness
        self.witness = sq(("var", witness))
        self.lines: list[str] = []
        self.count = 0

    def fresh(self) -> str:
        self.count += 1
        return f"sq_chain_{self.count}"

    def add_calc(self, start: Term, steps: list[tuple[Term, str]]) -> str:
        name = self.fresh()
        self.lines.append(f"have {name} : {term_to_str(start)} = {term_to_str(steps[-1][0])} := by")
        if len(steps) == 1:
            self.lines.append(f"  exact {steps[0][1]}")
        else:
            self.lines.append("  calc")
            for i, (to_term, proof) in enumerate(steps):
                self.lines.append(f"    {term_to_str(start) if i == 0 else '_'} = {term_to_str(to_term)} := {proof}")
        return name

    def reduce(self, t: Term) -> tuple[Term, str | None]:
        if t[0] == "var":
            return t, None
        ln, lp = self.reduce(t[1])
        rn, rp = self.reduce(t[2])
        cur = op(ln, rn)
        steps: list[tuple[Term, str]] = []
        if lp:
            steps.append((op(ln, t[2]), f"congrArg (fun u => u ◇ {term_to_str(t[2])}) {lp}"))
        if rp:
            steps.append((cur, f"congrArg (fun u => {term_to_str(ln)} ◇ u) {rp}"))
        while cur[0] == "op":
            l, r = cur[1], cur[2]
            if r[0] == "op" and r[1] == r[2]:
                cur = l
                steps.append((cur, f"right_id_square {term_to_str(l)} {term_to_str(r[1])}"))
            elif l[0] == "op" and l[1] == r:
                cur = l[2]
                steps.append((cur, f"sandwich {term_to_str(cur)} {term_to_str(r)}"))
            elif r[0] == "op" and r[2] == l:
                cur = r[1]
                steps.append((cur, f"left_sandwich {term_to_str(cur)} {term_to_str(l)}"))
            else:
                base = is_square(cur)
                if base is not None and cur != self.witness:
                    cur = self.witness
                    steps.append((cur, f"square_const {term_to_str(base)} {self.witness_var}"))
                else:
                    break
        if not steps:
            return t, None
        return cur, self.add_calc(t, steps)


def square_sandwich_chain_body(h_eq: dict[str, Any], g_eq: dict[str, Any]) -> str | None:
    helper = square_sandwich_helper_lines(h_eq, g_eq)
    if helper is None:
        return None
    reducer = SquareReducer(g_eq["variables"][0])
    lhs_norm, lhs_pf = reducer.reduce(g_eq["lhs"])
    rhs_norm, rhs_pf = reducer.reduce(g_eq["rhs"])
    if lhs_norm != rhs_norm:
        return None
    lines = helper + reducer.lines
    if lhs_pf is None and rhs_pf is None:
        lines.append("rfl")
    elif lhs_pf is None:
        lines.append(f"exact {rhs_pf}.symm")
    elif rhs_pf is None:
        lines.append(f"exact {lhs_pf}")
    else:
        lines.append(f"exact {lhs_pf}.trans {rhs_pf}.symm")
    return "\n".join(lines)


def rowconst_h(h_eq: dict[str, Any]):
    lhs, rhs = h_eq["lhs"], h_eq["rhs"]
    if lhs[0] != "op" or rhs[0] != "op":
        return None
    if lhs[1][0] != "var" or lhs[2][0] != "var" or rhs[1][0] != "var":
        return None
    x, y = lhs[1][1], lhs[2][1]
    if rhs[1][1] != y or rhs[2][0] != "op" or rhs[2][1][0] != "var" or rhs[2][2][0] != "op":
        return None
    z = rhs[2][1][1]
    if rhs[2][2] != op(("var", y), ("var", z)):
        return None
    return (x, y, z) if len({x, y, z}) == 3 else None


def rowconst_body(h_eq: dict[str, Any], g_eq: dict[str, Any]) -> str | None:
    m = rowconst_h(h_eq)
    if m is None or g_eq["lhs"][0] != "op" or g_eq["rhs"][0] != "op":
        return None
    hx, hy, hz = m

    def h_call(x: str, y: str, z: str) -> str:
        mp = {hx: x, hy: y, hz: z}
        return "h " + " ".join(lean_arg(mp[v]) for v in h_eq["variables"])

    lhs_l, lhs_r = term_to_str(g_eq["lhs"][1]), term_to_str(g_eq["lhs"][2])
    rhs_l, rhs_r = term_to_str(g_eq["rhs"][1]), term_to_str(g_eq["rhs"][2])
    return "\n".join([
        "intro " + " ".join(g_eq["variables"]),
        "have col : ∀ p q r : G, p ◇ q = r ◇ q := by",
        "  intro p q r",
        "  calc",
        f"    p ◇ q = q ◇ (q ◇ (q ◇ q)) := {h_call('p', 'q', 'q')}",
        f"    _ = r ◇ q := ({h_call('r', 'q', 'q')}).symm",
        "have rowconst : ∀ a b c : G, a ◇ b = a ◇ c := by",
        "  intro a b c",
        "  have hbcc : b ◇ c = c ◇ c := col b c c",
        "  calc",
        f"    a ◇ b = b ◇ (c ◇ (b ◇ c)) := {h_call('a', 'b', 'c')}",
        "    _ = c ◇ (c ◇ (b ◇ c)) := col b (c ◇ (b ◇ c)) c",
        "    _ = c ◇ (c ◇ (c ◇ c)) := by exact congrArg (fun u => c ◇ (c ◇ u)) hbcc",
        f"    _ = a ◇ c := ({h_call('a', 'c', 'c')}).symm",
        "calc",
        f"  {term_to_str(g_eq['lhs'])} = {rhs_l} ◇ {lhs_r} := col {lhs_l} {lhs_r} {rhs_l}",
        f"  _ = {term_to_str(g_eq['rhs'])} := rowconst {rhs_l} {lhs_r} {rhs_r}",
    ])


def square_rowconst_h(h_eq: dict[str, Any]) -> tuple[str, str, str] | None:
    lhs, rhs = h_eq["lhs"], h_eq["rhs"]
    if lhs[0] != "var" or rhs[0] != "op":
        return None
    x = lhs[1]
    left, right = rhs[1], rhs[2]
    if left != sq(("var", x)):
        return None
    if right[0] != "op" or right[2][0] != "var":
        return None
    yz = right[1]
    z = right[2][1]
    if yz[0] != "op" or yz[1][0] != "var" or yz[2] != ("var", z):
        return None
    y = yz[1][1]
    return (x, y, z) if len({x, y, z}) == 3 else None


def grounding_derived_body(h_eq: dict[str, Any], g_eq: dict[str, Any]) -> str | None:
    """Explicit square-rowconst close harvested from the grounding-derived sidecar.

    The old grounding-derived renderer can derive `∀ a b, a◇b = a◇a` on this
    shape but used to fail at a trailing `grind`. This packed version emits the
    final `calc` explicitly.
    """
    m = square_rowconst_h(h_eq)
    if m is None:
        return None
    hx, hy, hz = m
    lhs, rhs = g_eq["lhs"], g_eq["rhs"]
    if lhs[0] != "var" or rhs[0] != "op" or rhs[1] != sq(lhs):
        return None
    goal_x = term_to_str(lhs)
    rhs_inner = term_to_str(rhs[2])
    rhs_s = term_to_str(rhs)
    xx = f"({goal_x} ◇ {goal_x})"
    xxx = f"(({goal_x} ◇ {goal_x}) ◇ {goal_x})"

    def h_call(x: str, y: str, z: str) -> str:
        mp = {hx: x, hy: y, hz: z}
        return "h " + " ".join(lean_arg(mp[v]) for v in h_eq["variables"])

    lines = []
    if g_eq["variables"]:
        lines.append("intro " + " ".join(g_eq["variables"]))
    lines.extend([
        "have E1 : ∀ v0 v1 v2 v3 : G, (v0 ◇ v0) ◇ (v1 ◇ ((v2 ◇ v3) ◇ v3)) = v0 := by",
        "  intro v0 v1 v2 v3",
        f"  have ia := {h_call('v0', '(v1 ◇ v1)', '((v2 ◇ v3) ◇ v3)')}",
        f"  have ib := {h_call('v1', 'v2', 'v3')}",
        "  calc",
        "    (v0 ◇ v0) ◇ (v1 ◇ ((v2 ◇ v3) ◇ v3)) = (v0 ◇ v0) ◇ (((v1 ◇ v1) ◇ ((v2 ◇ v3) ◇ v3)) ◇ ((v2 ◇ v3) ◇ v3)) := by",
        "      exact congrArg (fun u => (v0 ◇ v0) ◇ (u ◇ ((v2 ◇ v3) ◇ v3))) ib",
        "    _ = v0 := ia.symm",
        "have E3 : ∀ v0 v1 v2 v3 : G, (v0 ◇ v0) ◇ v1 = v0 := by",
        "  intro v0 v1 v2 v3",
        "  have ia := E1 v0 (v1 ◇ v1) v2 v3",
        f"  have ib := {h_call('v1', 'v2', 'v3')}",
        "  calc",
        "    (v0 ◇ v0) ◇ v1 = (v0 ◇ v0) ◇ ((v1 ◇ v1) ◇ ((v2 ◇ v3) ◇ v3)) := by",
        "      exact congrArg (fun u => (v0 ◇ v0) ◇ u) ib",
        "    _ = v0 := ia",
        "have target : ∀ a b : G, a ◇ b = a ◇ a := by",
        "  intro a b",
        "  have ia := E3 (a ◇ a) b a a",
        "  have ib := E3 a (a ◇ a) a a",
        "  have bridge : ((a ◇ a) ◇ (a ◇ a)) ◇ b = a ◇ b := by",
        "    exact congrArg (fun u => u ◇ b) ib",
        "  exact bridge.symm.trans ia",
        "calc",
        f"  {goal_x} = {xx} ◇ {xxx} := {h_call(goal_x, goal_x, goal_x)}",
        f"  _ = {xx} ◇ {xx} := target {xx} {xxx}",
        f"  _ = {rhs_s} := (target {xx} {rhs_inner}).symm",
    ])
    return "\n".join(lines)


def battery_arg_layers(h_eq: dict[str, Any], g_eq: dict[str, Any]) -> list[dict[str, Any]]:
    nargs = len(h_eq["variables"])
    if nargs == 0:
        return []
    pad = (g_eq["variables"] or ["x"])[0]
    terms = goal_terms(g_eq, 12)
    compounds = [term for term in terms if "◇" in term]
    diag = tuple([pad] * nargs)

    def slot(i: int, term_list: list[str]) -> list[tuple[str, ...]]:
        rows = []
        for term in term_list:
            args = [pad] * nargs
            if i < nargs:
                args[i] = term
            rows.append(tuple(args))
        return rows

    layers: list[dict[str, Any]] = [{"name": "diag", "args": [diag]}]
    slot0 = unique_arg_rows([diag] + slot(0, terms))
    layers.append({"name": "slot0_terms", "args": slot0})
    slot1 = unique_arg_rows(slot0 + slot(1, compounds))
    layers.append({"name": "slot1_compounds", "args": slot1})
    if nargs >= 3:
        slot2 = unique_arg_rows(slot1 + slot(2, compounds))
        layers.append({"name": "slot2_compounds", "args": slot2})
    return layers


def proof_battery_graph_body(h_eq: dict[str, Any], g_eq: dict[str, Any], max_layers: int = 3) -> tuple[str | None, dict[str, Any]]:
    considered = []
    for layer in battery_arg_layers(h_eq, g_eq)[:max_layers]:
        rows = list(layer["args"])
        considered.append({"name": layer["name"], "arg_count": len(rows)})
        body = h_graph_body(h_eq, g_eq, limit=0, extra_args=rows)
        if body:
            return body, {
                "kind": "proof_battery_state",
                "status": "body_built",
                "winning_consumer": "battery_h_fact_graph",
                "graph_layers_considered": considered,
            }
    return None, {
        "kind": "proof_battery_state",
        "status": "no_graph_path",
        "graph_layers_considered": considered,
        "need_hint": "Old battery h-instance layers did not connect the goal; try forward_saturation, goal_superposition, or a midpoint.",
    }


def old_haves_grind_bodies(h_eq: dict[str, Any], g_eq: dict[str, Any]):
    """Yield staged HAVE+GRIND bodies from the generic h-instantiation pool.

    The 24-row body was the original cheap fallback.  A focused gap probe on
    held-out rows found that the same generator needs a slightly deeper
    prefix for some cases: `hard2_0021` closes at 48 generated instances and
    `hard3_0193` closes at 64.  Keep the stages separate so Lean can accept a
    cheap prefix before buying the larger grind context.
    """
    intro = "intro " + " ".join(g_eq["variables"]) if g_eq["variables"] else ""
    for limit in (24, 48, 64):
        haves = []
        rows = candidate_h_args(h_eq, g_eq, limit)
        for i, args in enumerate(rows, start=1):
            haves.append(f"have h{i} := h " + " ".join(map(lean_arg, args)))
        if intro and haves:
            yield f"old_haves_grind_{len(rows)}", "\n".join([intro, *haves, "grind"])


def proof_candidates_with_sources(h_eq: dict[str, Any], g_eq: dict[str, Any]):
    if g_eq["lhs"] == g_eq["rhs"]:
        yield "rfl_goal", "intro " + " ".join(g_eq["variables"]) + "\nrfl"
    for route, body in collapse_certificate_bodies(h_eq, g_eq):
        yield route, body
    for route, body in grounding_h_certificate_bodies(h_eq, g_eq):
        yield route, body
    for maker in (right_square_chain_body, generic_right_square_chain_body, square_sandwich_chain_body, rowconst_body, grounding_derived_body):
        try:
            body = maker(h_eq, g_eq)
        except Exception:
            body = None
        if body:
            yield maker.__name__.removesuffix("_body"), body
    body, _state = proof_battery_graph_body(h_eq, g_eq)
    if body:
        yield "proof_battery_graph", body
    for cfg in [(48, 0), (64, 0), (64, 600)]:
        body = h_graph_body(h_eq, g_eq, cfg[0], congruence_cap=cfg[1])
        if body:
            yield f"h_graph_limit_{cfg[0]}_cong_{cfg[1]}", body
    yield from native_saturation_bodies(h_eq, g_eq)
    yield from old_haves_grind_bodies(h_eq, g_eq)


def proof_candidates(h_eq: dict[str, Any], g_eq: dict[str, Any]):
    for _source, body in proof_candidates_with_sources(h_eq, g_eq):
        yield body


# LLM/tool-call fallback


def extract_json(text: str) -> dict[str, Any] | None:
    text = re.sub(r"<think>[\s\S]*?</think>", "", text or "").strip()
    text = re.sub(r"^```(?:json)?\s*\n?", "", text)
    text = re.sub(r"\n?```\s*$", "", text)
    try:
        data = json.loads(text)
        return data if isinstance(data, dict) else None
    except Exception:
        pass
    m = re.search(r"\{[\s\S]*\}", text)
    if m:
        try:
            data = json.loads(m.group())
            return data if isinstance(data, dict) else None
        except Exception:
            return None
    return None


def helper_kind(eq_text: str) -> str | None:
    try:
        eq = parse_equation(eq_text)
    except Exception:
        return None
    lhs, rhs = eq["lhs"], eq["rhs"]
    pairs = [(lhs, rhs), (rhs, lhs)]
    for l, r in pairs:
        if l[0] == "op" and r[0] == "var" and l[2] == sq(r):
            return "square_absorb"
        if l[0] == "op" and r[0] == "op" and r[1] == r[2] and l[2] == r[1]:
            return "right_square"
        if l[0] == "op" and r[0] == "op" and is_square(l) is not None and is_square(r) is not None and l != r:
            return "square_const"
        if l[0] == "op" and r[0] == "var":
            if l[2][0] == "op" and l[2][1] == l[2][2] and l[1] == r:
                return "right_id_square"
            if l[1][0] == "op" and l[1][2] == r and l[1][1] == l[2]:
                return "sandwich"
            if l[2][0] == "op" and l[2][1] == r and l[2][2] == l[1]:
                return "left_sandwich"
    return None


STANDARD_HELPER_CHAIN_SPECS: list[dict[str, Any]] = [
    {
        "name": "nested_tail_absorption",
        "trigger": "nested_tail_absorption",
        "budget_floor": 32.0,
        "budget_policy": {
            "initial_grant": 3.0,
            "max_grant": 15.0,
            "max_grants_per_task": 4,
        },
        "lemmas": [
            ("nested_absorb", "u ◇ (v ◇ u) = u"),
            ("tail_any", "((u ◇ v) ◇ v) ◇ (w ◇ t) = t"),
        ],
        "why": (
            "For H of the form x = (y ◇ (z ◇ x)) ◇ (w ◇ x), first prove "
            "`u ◇ (v ◇ u) = u`; with that helper, prove the broad tail law "
            "`((u ◇ v) ◇ v) ◇ (w ◇ t) = t`, which directly instantiates the goal."
        ),
    },
    {
        "name": "generic_right_square_absorption",
        "trigger": "repeated_self_absorption",
        "budget_floor": 12.0,
        "lemmas": [
            ("square_absorb", "u ◇ (v ◇ v) = v"),
            ("right_square", "u ◇ v = v ◇ v"),
        ],
        "why": (
            "A repeated self-absorption H can sometimes first prove "
            "`u ◇ (v ◇ v) = v`, then use it to prove `u ◇ v = v ◇ v`, "
            "and only then consume the pair toward a goal."
        ),
    },
]


def helper_chain_trigger_flags(h_eq: dict[str, Any], g_eq: dict[str, Any]) -> list[str]:
    flags: list[str] = []
    if nested_tail_absorption_h(h_eq, g_eq):
        flags.append("nested_tail_absorption")
    if repeated_self_absorption_h(h_eq, g_eq):
        flags.append("repeated_self_absorption")
    if special_right_square_h(h_eq):
        flags.append("focused_right_square_shape")
    if square_sandwich_h(h_eq):
        flags.append("focused_square_sandwich_shape")
    return flags


def selected_helper_chain_specs(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    call: dict[str, Any] | None = None,
) -> tuple[list[dict[str, Any]], list[str]]:
    call = call or {}
    requested_raw = call.get("chains") or call.get("chain") or call.get("families") or call.get("family")
    requested: set[str] = set()
    if isinstance(requested_raw, str):
        requested = {part.strip() for part in requested_raw.split(",") if part.strip()}
    elif isinstance(requested_raw, list):
        requested = {str(part).strip() for part in requested_raw if str(part).strip()}
    flags = helper_chain_trigger_flags(h_eq, g_eq)
    specs: list[dict[str, Any]] = []
    for spec in STANDARD_HELPER_CHAIN_SPECS:
        if requested and spec["name"] not in requested:
            continue
        if spec.get("trigger") in flags or requested:
            specs.append(spec)
    return specs, flags


def helper_chain_hints(spec: dict[str, Any]) -> list[UniversalEquation]:
    hints = []
    for name, equation in spec.get("lemmas", []):
        hints.append(UniversalEquation(name=name, eq=parse_equation(equation), extra_args=[]))
    return hints


def helper_chain_portfolio_attempt(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    call: dict[str, Any] | None = None,
    *,
    budget: float | None = None,
) -> tuple[str | None, dict[str, Any]]:
    """Try reusable helper chains through the generic midpoint consumer.

    This is a protocol-visible wrapper, not a separate proof engine: every
    helper is still proved from H and then consumed by the ordinary midpoint
    stitcher.  The wrapper only decides which canonical helper-chain shapes are
    worth trying for the current H/G.
    """
    call = call or {}
    specs, flags = selected_helper_chain_specs(h_eq, g_eq, call)
    total_budget = float(budget if budget is not None else call.get("budget") or call.get("time_budget") or 12.0)
    deadline = time.monotonic() + max(1.0, total_budget)
    attempts: list[dict[str, Any]] = []

    if not specs:
        return None, {
            "protocol_version": PROTOCOL_VERSION,
            "kind": "helper_chain_portfolio_state",
            "status": "not_applicable",
            "trigger_flags": flags,
            "available_chains": [spec["name"] for spec in STANDARD_HELPER_CHAIN_SPECS],
            "need_hint": "No standard helper-chain trigger fired; use lemma_chain with a problem-specific midpoint, goal_superposition, or false_model_search.",
        }

    for index, spec in enumerate(specs):
        rem = deadline - time.monotonic()
        if rem <= 0.5:
            attempts.append({
                "chain": spec["name"],
                "status": "skipped_budget_exhausted",
                "lemmas": [equation for _name, equation in spec.get("lemmas", [])],
            })
            continue

        hints = helper_chain_hints(spec)
        refuted = []
        for hint in hints:
            refutation = hint_refutation(h_eq, hint.eq)
            if refutation is not None:
                refuted.append({
                    "name": hint.name,
                    "equation": hint.eq["text"],
                    "refutation": refutation,
                })
        if refuted:
            attempts.append({
                "chain": spec["name"],
                "status": "refuted_by_small_model",
                "lemmas": [{"name": hint.name, "equation": hint.eq["text"]} for hint in hints],
                "refuted_lemmas": refuted,
            })
            continue

        remaining_specs = max(1, len(specs) - index)
        attempt_budget = min(rem, max(float(spec.get("budget_floor", 8.0)), rem / remaining_specs))
        raw_policy = dict(spec.get("budget_policy") or {})
        raw_policy["total_budget"] = attempt_budget
        body, state = generic_midpoint_chain_attempt(
            h_eq,
            g_eq,
            hints,
            budget_policy=raw_policy,
            total_budget=attempt_budget,
        )
        attempts.append({
            "chain": spec["name"],
            "status": "body_built" if body else state.get("status", "stuck"),
            "why": spec.get("why"),
            "budget": round(attempt_budget, 3),
            "lemmas": [{"name": hint.name, "equation": hint.eq["text"]} for hint in hints],
            "chain_state": state,
        })
        if body:
            return body, {
                "protocol_version": PROTOCOL_VERSION,
                "kind": "helper_chain_portfolio_state",
                "status": "body_built",
                "trigger_flags": flags,
                "winning_chain": spec["name"],
                "proved_lemmas": state.get("proved_lemmas", []),
                "attempts": attempts,
            }

    need_hint: Any = None
    for attempt in attempts:
        chain_state = attempt.get("chain_state")
        if isinstance(chain_state, dict) and chain_state.get("need_hint"):
            need_hint = chain_state.get("need_hint")
            break
    return None, {
        "protocol_version": PROTOCOL_VERSION,
        "kind": "helper_chain_portfolio_state",
        "status": "stuck",
        "trigger_flags": flags,
        "attempts": attempts,
        "need_hint": need_hint or {
            "kind": "helper_chain_repair",
            "reason": "Standard helper chains were plausible but did not close; propose a problem-specific lemma_chain using the closest proof/consume feedback.",
        },
    }


def helper_chain_portfolio_body(h_eq: dict[str, Any], g_eq: dict[str, Any]) -> str | None:
    body, _state = helper_chain_portfolio_attempt(h_eq, g_eq, budget=12.0)
    return body


def run_tool_call_detailed(
    call: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    *,
    capability_mask: Any = None,
    verify_candidates: bool = False,
) -> tuple[str | None, dict[str, Any] | None]:
    raw_tool = str(call.get("tool") or "").strip()
    tool = TOOL_ALIASES.get(raw_tool, raw_tool)
    gate_state = capability_gate_state(tool, capability_mask)
    if gate_state is not None:
        return None, gate_state
    if tool == "forward_saturation":
        bodies = list(native_saturation_bodies(h_eq, g_eq))
        attempts: list[dict[str, Any]] = []
        if verify_candidates:
            for idx, (route, body) in enumerate(bodies, start=1):
                result = judge_true_attributed(
                    f"llm:tool:forward_saturation:{route}",
                    body,
                    source="llm_tool_call",
                    detail={
                        "tool": "forward_saturation",
                        "candidate_index": idx,
                        "candidate_count": len(bodies),
                    },
                )
                attempts.append({
                    "route": route,
                    "status": result.get("status"),
                    "message": short_text(result.get("message") or result.get("stderr") or "", 300),
                })
                if result.get("status") == "accepted":
                    return body, protocol_state(
                        "MechanicalResponse",
                        "proved",
                        "forward_saturation",
                        tool=tool,
                        candidate_count=len(bodies),
                        accepted_route=route,
                        judge_attempts=attempts,
                        already_judged_accepted=True,
                    )
            return None, protocol_state(
                "MechanicalResponse",
                "stuck",
                "forward_saturation",
                tool=tool,
                candidate_count=len(bodies),
                judge_attempts=attempts,
                need_hint=(
                    "Forward saturation tried every generated body cheapest-first "
                    "and none closed; use closest_pairs to propose a midpoint, or "
                    "switch to goal_superposition."
                ),
            )

        body = bodies[0][1] if bodies else None
        route = bodies[0][0] if bodies else None
        return body, protocol_state(
            "MechanicalResponse",
            "candidate_generated" if body else "not_applicable",
            "forward_saturation",
            tool=tool,
            candidate_count=len(bodies),
            selected_route=route,
            need_hint=None if body else "No bounded saturation body was generated; try goal_superposition or a midpoint.",
        )
    if tool == "right_square_chain":
        body = right_square_chain_body(h_eq, g_eq)
        return body, protocol_state(
            "MechanicalResponse",
            "proved" if body else "not_applicable",
            "right_square_chain",
            tool=tool,
            need_hint=None if body else "Right-square focused renderer did not match; try lemma_chain or goal_superposition.",
        )
    if tool == "square_sandwich_chain":
        body = square_sandwich_chain_body(h_eq, g_eq)
        return body, protocol_state(
            "MechanicalResponse",
            "proved" if body else "not_applicable",
            "square_sandwich_chain",
            tool=tool,
            need_hint=None if body else "Square-sandwich renderer did not match; try lemma_chain with square_const/right_id/sandwich helpers.",
        )
    if tool == "helper_chain_portfolio":
        body, state = helper_chain_portfolio_attempt(
            h_eq,
            g_eq,
            call,
            budget=float(call.get("budget") or call.get("time_budget") or 12.0),
        )
        state = state or {}
        return body, protocolize_state(
            state,
            "helper_chain_portfolio",
            status="proved" if body else state.get("status", "stuck"),
        )
    if tool == "rowconst_certificates":
        body = rowconst_body(h_eq, g_eq)
        return body, protocol_state(
            "MechanicalResponse",
            "proved" if body else "not_applicable",
            "rowconst_certificates",
            tool=tool,
            need_hint=None if body else "Row-constant certificates did not apply; try standard_aux_superposition or a non-refuted midpoint from closest-equation feedback.",
        )
    if tool == "grounding_derived":
        body = grounding_derived_body(h_eq, g_eq)
        return body, protocolize_state({
            "kind": "grounding_derived_state",
            "status": "body_built" if body else "not_applicable",
            "derived_helper": "target : ∀ a b : G, a ◇ b = a ◇ a" if body else None,
            "need_hint": None if body else "Square-rowconst grounding closer did not apply; try certificates/rowconst/standard_aux or a midpoint.",
        }, "grounding_derived")
    if tool == "broad_grounding_derived":
        body, state = broad_grounding_derived_body(
            h_eq,
            g_eq,
            budget=float(call.get("budget") or call.get("time_budget") or 12.0),
            full_budget_per_target=bool(call.get("full_budget_per_target", False)),
        )
        state = state or {}
        return body, protocolize_state(state, "broad_grounding_derived", status="proved" if body else state.get("status", "stuck"))
    if tool == "collapse_certificates":
        bodies = list(collapse_certificate_bodies(h_eq, g_eq))
        body = bodies[0][1] if bodies else None
        return body, protocol_state(
            "MechanicalResponse",
            "proved" if body else "not_applicable",
            "collapse_certificates",
            tool=tool,
            candidate_count=len(bodies),
            need_hint=None if body else "No carrier-collapse witness was derived within the bounded certificate search; try standard_aux_superposition, goal_superposition, or a midpoint.",
        )
    if tool == "grounding_h":
        bodies = list(grounding_h_certificate_bodies(h_eq, g_eq))
        body = bodies[-1][1] if bodies else None
        return body, protocol_state(
            "MechanicalResponse",
            "proved" if body else "not_applicable",
            "grounding_h",
            tool=tool,
            candidate_count=len(bodies),
            need_hint=None if body else "H is not non-orientable, or the goal has no variables; try standard_aux_superposition or a midpoint.",
        )
    if tool == "deep_saturation":
        bodies = list(native_saturation_bodies(h_eq, g_eq))
        body = bodies[-1][1] if bodies else None
        return body, protocol_state(
            "MechanicalResponse",
            "proved" if body else "not_applicable",
            "deep_saturation",
            tool=tool,
            candidate_count=len(bodies),
            need_hint=None if body else "No bounded saturation body was generated; try goal_superposition or a midpoint.",
        )
    if tool == "proof_battery":
        max_layers = int(call.get("max_graph_candidates") or call.get("graph_candidates") or 3)
        body, state = proof_battery_graph_body(h_eq, g_eq, max_layers=max(1, min(max_layers, 8)))
        state = state or {}
        return body, protocolize_state(state, "proof_battery", status="proved" if body else state.get("status", "stuck"))
    if tool == "goal_superposition":
        body, state = superposition_prove_detailed(
            h_eq,
            g_eq,
            budget=float(call.get("budget") or call.get("time_budget") or 8.0),
            allow_var_overlap=bool(call.get("allow_var_overlap", False)),
        )
        state = state or {}
        return body, protocolize_state(state, "goal_superposition", status="proved" if body else state.get("status", "stuck"))
    if tool == "standard_aux_superposition":
        body, state = standard_aux_superposition_attempt(h_eq, g_eq, call)
        state = state or {}
        return body, protocolize_state(state, "standard_aux_superposition", status="proved" if body else state.get("status", "stuck"))
    if tool in {"lemma_chain", "lemma_hint", "midpoint", "midpoint_chain"}:
        body, state = hint_payload_attempt(call, h_eq, g_eq, capability_mask=capability_mask)
        state = state or {}
        return body, protocolize_state(state, "generic_midpoint_chain", status="proved" if body else state.get("status", "stuck"))
    if tool == "false_model_family":
        found, state = false_model_family_attempt(h_eq, g_eq, call)
        state = dict(state or {})
        state["candidate_ready"] = found is not None
        return None, state
    if tool == "infinite_model_artifact":
        _code, state = validate_infinite_model_payload(call)
        return None, state
    return None, protocol_state(
        "MechanicalResponse",
        "unsupported_tool",
        "tool_registry",
        tool=raw_tool,
        need_hint="Choose one supported tool from the registry, or return a midpoint/lemma_chain/false_model_search/false_model_family action.",
    )


def run_tool_call(call: dict[str, Any], h_eq: dict[str, Any], g_eq: dict[str, Any]):
    body, _state = run_tool_call_detailed(call, h_eq, g_eq)
    return body


def standard_aux_plausible_h(h_eq: dict[str, Any]) -> bool:
    return bool(one_sided_variables(h_eq))


def analysis(h_eq: dict[str, Any], g_eq: dict[str, Any]) -> str:
    advice = []
    advice.append("General midpoint engine is available: propose one small equation M or a short chain; each must be proved from H before use.")
    advice.append("Broad true-side consumer available: goal_superposition runs bounded proof-carrying paramodulation and reports a frontier if it gets stuck.")
    advice.append("Broad grounding certificates available: broad_grounding_derived tries to derive collapse or factor-irrelevance helpers and then close G.")
    advice.append("Standard auxiliary consumer available: standard_aux_superposition tries const/projection/rowconst lemmas as explicit proved helpers.")
    advice.append("Helper-chain portfolio available: helper_chain_portfolio tries a small set of reusable lemma chains through the generic midpoint stitcher and reports proved-but-not-consumed chains.")
    if goal_generalization_actions(h_eq, g_eq):
        advice.append("Goal-generalization cards are active: G appears to be a special case of a stronger reusable law, so try proving the reusable law first.")
    one_sided = one_sided_variables(h_eq)
    if one_sided:
        advice.append(f"H has variables on only one side {one_sided}; standard_aux_superposition is a strong next tool because these often imply collapse/projection/rowconst helpers.")
    if h_eq["lhs"][0] == "var" or h_eq["rhs"][0] == "var":
        advice.append("H has a lone-variable side; collapse_certificates may derive a carrier-collapse witness and close the whole goal.")
    if self_root_absorption_h(h_eq):
        advice.append("H has self-root absorption form x = x ◇ T or x = T ◇ x; broad_grounding_derived gets a stronger helper-derivation budget.")
    if repeated_self_absorption_h(h_eq, g_eq):
        advice.append("H has repeated self-absorption form x = T[x,x,...] and G is x = compound; prefer an early true-side midpoint/lemma_chain before expensive false search.")
    if nested_tail_absorption_h(h_eq, g_eq):
        advice.append("H has nested-tail absorption form x = (y ◇ (z ◇ x)) ◇ (w ◇ x); try nested_absorb then the broad tail_any contraction helper.")
    if special_right_square_h(h_eq):
        advice.append("H matches right_square_chain: try helpers u ◇ (v ◇ v)=v and u ◇ v=v ◇ v.")
    if square_sandwich_h(h_eq):
        advice.append("H matches square_sandwich_chain: try square_const/right_id_square/sandwich helpers.")
    if rowconst_h(h_eq):
        advice.append("H matches rowconst_certificates.")
    if square_rowconst_h(h_eq):
        advice.append("H matches grounding_derived square-rowconst: derive a ◇ b = a ◇ a and close explicitly.")
    advice.append("If false, use false_model_search for fixed routes or false_model_family for a compact LLM-proposed finite operation. Family proposals are expanded and checked mechanically; failed families return H violations, G failures, and hot operation cells.")
    return "\n".join(advice)


def problem_analysis(h_eq: dict[str, Any], g_eq: dict[str, Any]) -> str:
    h_args = " ".join(h_eq["variables"])
    schema_args = [v.upper() for v in h_eq["variables"]]
    schema_lhs = term_to_str_subst(h_eq["lhs"], dict(zip(h_eq["variables"], schema_args)))
    schema_rhs = term_to_str_subst(h_eq["rhs"], dict(zip(h_eq["variables"], schema_args)))
    lines = [
        f"h variables, in call order: {h_eq['variables']}",
        f"goal variables, introduce in this order if writing proof: {g_eq['variables']}",
        f"`h {h_args}` has type: {h_eq['text']}",
        f"schematically, h {' '.join(schema_args)} gives: {schema_lhs} = {schema_rhs}",
        "goal subterms worth bridging: " + ", ".join(goal_terms(g_eq, 8)),
        "strict symbolic-family prefilter: " + json.dumps(
            symbolic_invariant_report(h_eq, g_eq),
            ensure_ascii=False,
        ),
    ]
    return "\n".join(lines)


def tool_registry_text(capability_mask: Any = None, *, include_research_tools: bool = False) -> str:
    normalized_mask = normalize_capability_mask(capability_mask)
    disabled = set(normalized_mask["disabled"])
    rows = []
    for name, spec in TOOL_REGISTRY.items():
        if spec.get("deployability") == "research_only" and not include_research_tools:
            continue
        required = required_capabilities_for_tool(name)
        available = not any(capability in disabled for capability in required)
        if not available:
            continue
        row = {
            "tool": name,
            "domain": spec["domain"],
            "scope": spec.get("scope", "whole_goal"),
            "cost": spec.get("cost", "medium"),
            "feedback_quality": spec.get("feedback_quality", "basic"),
            "native_import": spec.get("native_import", "collaborative"),
            "aliases": spec.get("aliases", [])[:4],
            "description": spec["description"],
        }
        if capability_mask is not None:
            row["capability"] = f"tool:{name}"
            row["required_capabilities"] = required
        rows.append(row)
    return json.dumps(rows, ensure_ascii=False)


def sidecar_fewshots(h_eq: dict[str, Any]) -> str:
    nargs = len(h_eq["variables"])
    example_args = ["x"] * nargs
    return "\n".join([
        "If H has right-square absorption shape, use:",
        '{"kind":"tool_call","tool":"right_square_chain","target":"goal","budget":15}',
        "or the generic helper chain:",
        '{"kind":"tool_call","tool":"lemma_chain","target":"goal","lemmas":[{"name":"square_absorb","equation":"u ◇ (v ◇ v) = v"},{"name":"right_square","equation":"u ◇ v = v ◇ v"}]}',
        "If H has repeated self-absorption but does not match a focused renderer, try the standard helper-chain portfolio:",
        '{"kind":"tool_call","tool":"helper_chain_portfolio","target":"goal","chains":["generic_right_square_absorption"],"budget":12}',
        "If H has nested-tail absorption x = (y ◇ (z ◇ x)) ◇ (w ◇ x), use:",
        '{"kind":"tool_call","tool":"helper_chain_portfolio","target":"goal","chains":["nested_tail_absorption"],"budget":36}',
        "If H has square-witness/sandwich shape, use:",
        '{"kind":"tool_call","tool":"lemma_chain","target":"goal","lemmas":[{"name":"square_const","equation":"u ◇ u = v ◇ v"},{"name":"right_id_square","equation":"u ◇ (v ◇ v) = u"},{"name":"sandwich","equation":"(v ◇ u) ◇ v = u"},{"name":"left_sandwich","equation":"v ◇ (u ◇ v) = u"}]}',
        "If H has square-rowconst grounding shape, use:",
        '{"kind":"tool_call","tool":"grounding_derived","target":"goal","budget":12}',
        "If H is orientable but seems to need a derived collapse/factor-irrelevance helper, use:",
        '{"kind":"tool_call","tool":"broad_grounding_derived","target":"goal","budget":12}',
        "If shallow h-instances almost connect the goal, use graph-first proof battery:",
        '{"kind":"tool_call","tool":"proof_battery","target":"goal","max_graph_candidates":3}',
        "If feedback asks for a bridge, use lemma_hint with equations and optional seed_h_args:",
        json.dumps({"kind": "tool_call", "tool": "lemma_hint", "target": "goal", "lemmas": [{"equation": "<left frontier> = <right frontier>", "seed_h_args": [example_args]}]}, ensure_ascii=False),
        "If graph search is stuck and no focused family applies, try broad proof-carrying superposition:",
        '{"kind":"tool_call","tool":"goal_superposition","target":"goal","budget":8}',
        "If the goal may collapse under a standard lemma, try auxiliary superposition:",
        '{"kind":"tool_call","tool":"standard_aux_superposition","target":"goal","lemmas":["const","proj_l","proj_r","rowconst"],"budget":10}',
        "If feedback says a stronger helper was refuted_by_small_model, do not repeat that helper; use the closest non-refuted bridge instead.",
        "Repair example: if a projection-like target has the same left prefix on both sides, propose a reusable right-argument contraction:",
        '{"kind":"midpoint","lemma":"a ◇ ((b ◇ c) ◇ d) = a ◇ b","why":"connects a left-prefix goal by contracting the right argument; mechanical side will prove and consume it"}',
        "Repair example: if feedback says rowconst was the target but direct opconst is not refuted, opconst can be a useful stronger bridge:",
        '{"kind":"midpoint","lemma":"a ◇ b = c ◇ d","why":"derived opconst-like bridge was not refuted and would consume row/product goals"}',
        "Repair example: if rowconst `a ◇ b = a ◇ c` is proved but not consumed, add a non-refuted follow-up helper rather than repeating rowconst alone:",
        '{"kind":"tool_call","tool":"lemma_chain","target":"goal","lemmas":[{"name":"rowconst","equation":"a ◇ b = a ◇ c"},{"name":"right_contract","equation":"a ◇ ((b ◇ c) ◇ d) = a ◇ b"}]}',
        "Repair example: if one projection is proved but not consumed, add the opposite projection in the same lemma_chain:",
        '{"kind":"tool_call","tool":"lemma_chain","target":"goal","lemmas":[{"name":"proj_l","equation":"a ◇ b = a"},{"name":"proj_r","equation":"a ◇ b = b"}]}',
        "Projection warning: a proved closest-pair midpoint can still be too goal-specific; if projection-shaped feedback is visible, prefer the reusable projection pair.",
        "If feedback says a projection aux was proved but not consumed, ask standard_aux_superposition for the opposite projection too:",
        '{"kind":"tool_call","tool":"standard_aux_superposition","target":"goal","lemmas":["proj_l","proj_r"],"budget":10}',
        "If H has repeated self-absorption form x = T[x,x,...], use a short concrete lemma_chain of absorption/contraction bridges instead of repeating the whole goal as one midpoint:",
        '{"kind":"tool_call","tool":"lemma_chain","target":"goal","lemmas":[{"name":"absorb_step","equation":"<fill from closest_pairs>"},{"name":"goal_bridge","equation":"<fill from the remaining gap>"}]}',
        "Repair example: for right-square absorption, do not stop after one helper; use the two-lemma chain:",
        '{"kind":"tool_call","tool":"lemma_chain","target":"goal","lemmas":[{"name":"square_absorb","equation":"u ◇ (v ◇ v) = v"},{"name":"right_square","equation":"u ◇ v = v ◇ v"}]}',
        "Repair example: for square-sandwich hypotheses, square_const/right_id alone may be proved_not_consumed; add sandwich helpers:",
        '{"kind":"tool_call","tool":"lemma_chain","target":"goal","lemmas":[{"name":"square_const","equation":"u ◇ u = v ◇ v"},{"name":"right_id_square","equation":"u ◇ (v ◇ v) = u"},{"name":"sandwich","equation":"(v ◇ u) ◇ v = u"},{"name":"left_sandwich","equation":"v ◇ (u ◇ v) = u"}]}',
        "Repair example: if a proposed midpoint simply repeats the target goal, replace it with reusable helper lemmas; for square-sandwich feedback use the four-lemma chain above.",
        "If false, prefer concrete untried routes:",
        '{"kind":"tool_call","tool":"false_model_search","target":"goal","template":"local_search","routes":["local_search:n=6:seed=2"],"budget":6}',
        "Natural false-search hints are also accepted:",
        '{"kind":"false_model_hint","template":"local_search","sizes":[5,6,7],"seeds":[0,1,2],"time_budget":12}',
        "For deterministic native witness families, use:",
        '{"kind":"tool_call","tool":"false_model_search","target":"goal","routes":["structured_ce:max_n=7"],"budget":8}',
        "If false and a complete small-size check is useful, ask for propagation model finding:",
        '{"kind":"tool_call","tool":"false_model_search","target":"goal","template":"model_finder","routes":["model_finder:n=4"],"budget":6}',
        "If false and ordinary finite search is sparse, ask for the goal-directed model finder:",
        '{"kind":"tool_call","tool":"false_model_search","target":"goal","template":"model_finder_v2","routes":["model_finder_v2:n=6"],"budget":8}',
        "If exact finite-domain CP-SAT is available and small sizes need proof/witness search, ask for:",
        '{"kind":"tool_call","tool":"false_model_search","target":"goal","template":"cp_sat","routes":["cp_sat:n=5"],"budget":10}',
        "If ordinary table search stalls, try a compact quotient-by-fiber extension. A 2x3 route synthesizes a two-element quotient and affine local maps on three-element fibers; a failed state recommends changed factors:",
        '{"kind":"tool_call","tool":"false_model_search","target":"goal","template":"skew_product","routes":["skew_product:2x3"],"budget":4}',
        '{"kind":"tool_call","tool":"false_model_search","target":"goal","template":"sympy_sat","routes":["sympy_sat:n=6"],"budget":120}',
        "If false may need a structured larger witness, ask for polynomial magma search:",
        '{"kind":"tool_call","tool":"false_model_search","target":"goal","template":"poly_ce","routes":["poly_ce:tier=2:nmax=13"],"budget":8}',
        "If fixed routes are exhausted, propose one coherent finite operation family. Prefer residue/block/diagonal/affine rules over arbitrary patches:",
        '{"kind":"false_model_family","carrier_size":8,"default":{"kind":"affine","params":[1,0,0]},"rules":[{"when":{"kind":"diagonal"},"value":"i+1"}],"budget":8}',
        "If family feedback says repair_h_preserve_g, keep the G-breaking example and change rules touching h_profile.hot_cells. If it says break_g_preserve_h, preserve the default law and add one coherent region that separates the goal.",
    ])


def tool_advice(h_eq: dict[str, Any], g_eq: dict[str, Any], prefer_false: bool = False) -> str:
    ranked = []
    for invariant in symbolic_invariant_report(h_eq, g_eq):
        action = invariant.get("action")
        if invariant.get("separates_goal") and isinstance(action, dict):
            ranked.append({
                "tool": "false_model_family",
                "score": 100,
                "why": (
                    f"Strict {invariant['family']} invariant satisfies H and separates G: "
                    f"{invariant['reason']}."
                ),
                "call": action,
            })
    for item in goal_generalization_actions(h_eq, g_eq):
        action = item["action"]
        ranked.append({
            "tool": action.get("tool") or action.get("kind", "midpoint"),
            "score": 96,
            "why": item["reason"],
            "strategy_card": item["card"],
            "call": action,
        })
    for action in right_context_contraction_actions(h_eq, g_eq):
        ranked.append({
            "tool": "lemma_hint",
            "score": 91,
            "why": "Goal differs only by a right argument under a shared left prefix; try this non-refuted reusable contraction helper.",
            "call": action,
        })
    if right_square_chain_body(h_eq, g_eq) or special_right_square_h(h_eq):
        ranked.append({"tool": "right_square_chain", "score": 98, "why": "H/G match the trusted right-square absorption helper-chain renderer.", "call": {"kind": "tool_call", "tool": "right_square_chain", "target": "goal", "budget": 15}})
        ranked.append({"tool": "lemma_chain", "score": 90, "why": "Same proof through generic helper-chain consumer.", "call": {"kind": "tool_call", "tool": "lemma_chain", "target": "goal", "lemmas": [
            {"name": "square_absorb", "equation": "u ◇ (v ◇ v) = v"},
            {"name": "right_square", "equation": "u ◇ v = v ◇ v"},
        ]}})
    if repeated_self_absorption_h(h_eq, g_eq):
        ranked.append({"tool": "helper_chain_portfolio", "score": 93, "why": "H has repeated self-absorption; try reusable helper chains through the generic midpoint consumer and use their proved/not-consumed feedback.", "call": {"kind": "tool_call", "tool": "helper_chain_portfolio", "target": "goal", "chains": ["generic_right_square_absorption"], "budget": 12}})
    if nested_tail_absorption_h(h_eq, g_eq):
        ranked.append({"tool": "helper_chain_portfolio", "score": 97, "why": "H has nested-tail absorption; prove nested_absorb, then the broad tail_any contraction law and instantiate it to G.", "call": {"kind": "tool_call", "tool": "helper_chain_portfolio", "target": "goal", "chains": ["nested_tail_absorption"], "budget": 36}})
    if square_sandwich_h(h_eq):
        ranked.append({"tool": "lemma_chain", "score": 98, "why": "H has the square-witness/sandwich shape; use the four-helper chain.", "call": {"kind": "tool_call", "tool": "lemma_chain", "target": "goal", "lemmas": [
            {"name": "square_const", "equation": "u ◇ u = v ◇ v"},
            {"name": "right_id_square", "equation": "u ◇ (v ◇ v) = u"},
            {"name": "sandwich", "equation": "(v ◇ u) ◇ v = u"},
            {"name": "left_sandwich", "equation": "v ◇ (u ◇ v) = u"},
        ]}})
        ranked.append({"tool": "square_sandwich_chain", "score": 92, "why": "Focused equivalent renderer for the square-witness helper chain.", "call": {"kind": "tool_call", "tool": "square_sandwich_chain", "target": "goal", "budget": 15}})
    if rowconst_h(h_eq):
        ranked.append({"tool": "rowconst_certificates", "score": 85, "why": "H matches a row-constant certificate pattern.", "call": {"kind": "tool_call", "tool": "rowconst_certificates", "target": "goal"}})
    if square_rowconst_h(h_eq):
        ranked.append({"tool": "grounding_derived", "score": 84, "why": "H matches square-rowconst grounding; derive/use a◇b=a◇a with an explicit final close.", "call": {"kind": "tool_call", "tool": "grounding_derived", "target": "goal", "budget": 12}})
    if h_eq["lhs"][0] == "var" or h_eq["rhs"][0] == "var":
        ranked.append({"tool": "collapse_certificates", "score": 72, "why": "H has a lone-variable side; try deriving a carrier-collapse witness and closing the goal from triviality.", "call": {"kind": "tool_call", "tool": "collapse_certificates", "target": "goal", "budget": 12}})
    if broad_grounding_orientable(h_eq["lhs"], h_eq["rhs"]):
        bg_score = 86 if self_root_absorption_h(h_eq) else 74
        bg_why = (
            "H has self-root absorption form; derive a factor-irrelevance helper with the broad grounding certificate route."
            if self_root_absorption_h(h_eq)
            else "H is orientable; try deriving a collapse or factor-irrelevance helper and let Lean close the goal."
        )
        ranked.append({"tool": "broad_grounding_derived", "score": bg_score, "why": bg_why, "call": {"kind": "tool_call", "tool": "broad_grounding_derived", "target": "goal", "budget": 12}})
    ranked.append({"tool": "proof_battery", "score": 46, "why": "Try old battery h-instance layers through the explicit equality graph before risky grind bodies.", "call": {"kind": "tool_call", "tool": "proof_battery", "target": "goal", "max_graph_candidates": 3}})
    aux_score = 88 if standard_aux_plausible_h(h_eq) else 42
    aux_why = (
        "H has variables on only one side; try collapse/projection/rowconst lemmas through proof-carrying superposition."
        if standard_aux_plausible_h(h_eq)
        else "Try standard collapse/projection/rowconst lemmas through proof-carrying superposition and consume any proved helper."
    )
    ranked.append({"tool": "standard_aux_superposition", "score": aux_score, "why": aux_why, "call": {"kind": "tool_call", "tool": "standard_aux_superposition", "target": "goal", "lemmas": ["const", "proj_l", "proj_r", "rowconst"], "budget": 10}})
    ranked.append({"tool": "lemma_hint", "score": 50, "why": "Use closest_pairs from mechanical feedback to propose a concrete bridge equation; never return the placeholder text.", "call": {"kind": "tool_call", "tool": "lemma_hint", "target": "goal", "lemmas": ["<small bridge equation>"]}})
    ranked.append({"tool": "forward_saturation", "score": 45, "why": "Try extra h-instantiation seed terms near the frontier.", "call": {"kind": "tool_call", "tool": "forward_saturation", "target": "goal", "seed_terms": goal_terms(g_eq, 4), "budget": 3}})
    ranked.append({"tool": "goal_superposition", "score": 43, "why": "Broad proof-carrying paramodulation consumer; useful when graph search needs unification-on-demand.", "call": {"kind": "tool_call", "tool": "goal_superposition", "target": "goal", "budget": 8}})
    false_routes = (
        [
            "local_search:n=6:seed=0",
            "local_search:n=6:seed=1",
            "local_search:n=7:seed=0",
            "model_finder_v2:n=7",
            "model_finder_v2:n=8",
            "sympy_sat:n=6",
            "skew_product:2x3",
            "cp_sat:n=5",
            "cp_sat:n=6",
            "poly_ce:tier=2:nmax=13",
            "structured_ce:max_n=7",
        ]
        if prefer_false
        else ["model_finder_v2:n=5", "skew_product:2x3", "local_search:n=6:seed=2", "poly_ce:tier=2:nmax=13", "structured_ce:max_n=7"]
    )
    ranked.append({"tool": "false_model_search", "score": 94 if prefer_false else 40, "why": "Prefer concrete finite-countermodel routes now; true-side tools have already failed or are low-confidence." if prefer_false else "Try bounded finite countermodel routes if false is plausible; model_finder_v2 gives goal-directed Skolem feedback and poly_ce can find structured larger witnesses.", "call": {"kind": "tool_call", "tool": "false_model_search", "target": "goal", "routes": false_routes, "budget": 12 if prefer_false else 8}})
    ranked.append({
        "tool": "false_model_family",
        "score": 92 if prefer_false else 35,
        "why": "Propose a compact finite operation family when fixed routes are exhausted; the consumer returns exact H/G repair diagnostics.",
        "call": {
            "kind": "false_model_family",
            "carrier_size": 8,
            "default": {"kind": "affine", "params": [1, 0, 0]},
            "rules": [{"when": {"kind": "diagonal"}, "value": "i + 1"}],
            "budget": 8,
        },
    })
    ranked.sort(key=lambda item: item["score"], reverse=True)
    return json.dumps({
        "kind": "tool_recommendations",
        "recommended_next_action": ranked[0]["call"] if ranked else None,
        "ranked": ranked[:6],
    }, ensure_ascii=False)


def try_true(body: str) -> bool:
    result = call_judge("true", make_true_code(body))
    return result.get("status") == "accepted"


def try_false(n: int, table: list[list[int]]) -> bool:
    result = call_judge("false", make_false_code(n, table))
    return result.get("status") == "accepted"


def try_false_artifact(found: tuple[Any, ...]) -> bool:
    n = int(found[0])
    table = found[1]
    if len(found) >= 3 and isinstance(found[2], str) and found[2].strip():
        result = call_judge("false", make_false_formula_code(n, found[2]))
        if result.get("status") == "accepted":
            return True
    return try_false(n, table)


def emit_attribution_attempt(route: str, verdict: str, *, source: str = "baby_solver", detail: dict[str, Any] | None = None) -> None:
    payload = {
        "protocol_version": PROTOCOL_VERSION,
        "event": "judge_attempt",
        "route": route,
        "verdict": verdict,
        "source": source,
    }
    if detail:
        payload["detail"] = detail
    print("ATTRIBUTION " + json.dumps(payload, ensure_ascii=False, sort_keys=True), file=sys.stderr, flush=True)


def judge_true_attributed(route: str, body: str, *, source: str = "baby_solver", detail: dict[str, Any] | None = None) -> dict[str, Any]:
    emit_attribution_attempt(route, "true", source=source, detail=detail)
    return call_judge("true", make_true_code(body))


def try_true_attributed(route: str, body: str, *, source: str = "baby_solver", detail: dict[str, Any] | None = None) -> bool:
    result = judge_true_attributed(route, body, source=source, detail=detail)
    return result.get("status") == "accepted"


def try_false_attributed(route: str, n: int, table: list[list[int]], *, source: str = "baby_solver", detail: dict[str, Any] | None = None) -> bool:
    emit_attribution_attempt(route, "false", source=source, detail=detail)
    return try_false(n, table)


def try_false_artifact_attributed(route: str, found: tuple[Any, ...], *, source: str = "baby_solver", detail: dict[str, Any] | None = None) -> bool:
    n = int(found[0])
    table = found[1]
    if len(found) >= 3 and isinstance(found[2], str) and found[2].strip():
        emit_attribution_attempt(f"{route}:formula", "false", source=source, detail=detail)
        result = call_judge("false", make_false_formula_code(n, found[2]))
        if result.get("status") == "accepted":
            return True
    emit_attribution_attempt(f"{route}:table", "false", source=source, detail=detail)
    return try_false(n, table)


def judge_infinite_model_artifact_attributed(
    route: str,
    code: str,
    *,
    source: str = "research_protocol",
    detail: dict[str, Any] | None = None,
) -> dict[str, Any]:
    emit_attribution_attempt(route, "false", source=source, detail={
        "certificate_class": "infinite_model",
        "artifact_bytes": len(code.encode("utf-8")),
        **(detail or {}),
    })
    return call_judge("false", code)


def is_hint_payload(data: dict[str, Any]) -> bool:
    tool = TOOL_ALIASES.get(str(data.get("tool") or "").strip(), data.get("tool"))
    if data.get("kind") == "tool_call" and tool not in {"lemma_chain", "lemma_hint", "midpoint", "midpoint_chain"}:
        return False
    return (
        tool in {"lemma_chain", "lemma_hint", "midpoint", "midpoint_chain"}
        or data.get("kind") in {"midpoint", "midpoint_chain", "lemma_hint", "lemma_chain"}
        or any(key in data for key in ("lemma", "lemmas", "midpoint", "midpoints"))
    )


def cap_hint_payload_budget(data: dict[str, Any], cap: float | None) -> dict[str, Any]:
    if cap is None:
        return data
    cap_value = max(1.0, float(cap))
    out = dict(data)
    for key in ("budget", "time_budget"):
        if key in out:
            out[key] = min(_finite_float(out.get(key), cap_value), cap_value)
    if "budget" not in out and "time_budget" not in out:
        out["budget"] = cap_value
    raw_policy = out.get("budget_policy")
    policy = dict(raw_policy) if isinstance(raw_policy, dict) else {}
    policy["total_budget"] = min(_finite_float(policy.get("total_budget", policy.get("total")), cap_value), cap_value)
    policy["max_grant"] = min(_finite_float(policy.get("max_grant"), min(4.0, cap_value)), cap_value)
    policy["initial_grant"] = min(_finite_float(policy.get("initial_grant", policy.get("minimum_grant")), 2.0), policy["max_grant"])
    policy["max_grants_per_task"] = min(_clamped_int(policy.get("max_grants_per_task"), 2, 1, 8), 3)
    out["budget_policy"] = policy
    return out


def generic_projection_hint_kind(eq: dict[str, Any]) -> str | None:
    """Classify broad collapse hints that are often stale in false phases."""
    for lhs, rhs in ((eq["lhs"], eq["rhs"]), (eq["rhs"], eq["lhs"])):
        if lhs[0] == "var" and rhs[0] == "var" and lhs != rhs:
            return "const"
        if lhs[0] == "op" and rhs[0] == "var":
            if rhs == lhs[1]:
                return "proj_l"
            if rhs == lhs[2]:
                return "proj_r"
    return None


def is_generic_projection_hint_payload(data: dict[str, Any]) -> bool:
    hints = parse_universal_equations(data)
    if not hints:
        return False
    kinds = [generic_projection_hint_kind(hint.eq) for hint in hints]
    return all(kind in {"const", "proj_l", "proj_r"} for kind in kinds)


def is_false_model_payload(data: dict[str, Any]) -> bool:
    tool = TOOL_ALIASES.get(str(data.get("tool") or "").strip(), data.get("tool"))
    kind = str(data.get("kind") or "").strip()
    template = str(data.get("template") or "").strip().lower()
    return bool(
        tool == "false_model_search"
        or kind in {"false_model_search", "false_model_hint", "countermodel_hint", "false_table_search"}
        or template in {
            "local_search",
            "model_finder",
            "model_finder_v2",
            "goal_directed",
            "goal_directed_model_finder",
            "poly",
            "poly_ce",
            "polynomial",
            "cp_sat",
            "cpsat",
            "constraint_sat",
            "skew_product",
            "skew",
            "block_model",
            "structured_ce",
            "ce_engine",
            "witness_families",
        }
    )


def is_false_model_family_payload(data: dict[str, Any]) -> bool:
    tool = TOOL_ALIASES.get(str(data.get("tool") or "").strip(), data.get("tool"))
    kind = str(data.get("kind") or "").strip()
    return bool(
        tool == "false_model_family"
        or kind in {
            "false_model_family",
            "symbolic_countermodel",
            "symbolic_model",
            "finite_model_family",
        }
    )


def is_infinite_model_payload(data: dict[str, Any]) -> bool:
    tool = TOOL_ALIASES.get(str(data.get("tool") or "").strip(), data.get("tool"))
    kind = str(data.get("kind") or "").strip()
    return bool(
        tool == "infinite_model_artifact"
        or kind in {"infinite_model", "infinite_countermodel", "infinite_model_artifact"}
    )


SYMBOLIC_MODEL_PLAN_VERSION = "sair-symbolic-model-plan-v1"
SYMBOLIC_MODEL_PLAN_KINDS = {
    "symbolic_model_plan",
    "type_model_plan",
    "infinite_model_plan",
    "structured_infinite_model",
}
SYMBOLIC_MODEL_PATCH_KINDS = {
    "symbolic_model_patch",
    "type_model_patch",
    "infinite_model_patch",
    "structured_infinite_model_patch",
}
SYMBOLIC_MODEL_PART_FIELDS = (
    "carrier",
    "definitions",
    "operation",
    "setup",
    "hypothesis_proof",
    "counterexample_proof",
)
_SYMBOLIC_MODEL_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
_SYMBOLIC_MODEL_IMPORT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")
_SYMBOLIC_MODEL_BANNED_RE = re.compile(
    r"\b(?:sorry|admit|axiom|unsafe|def\s+submission)\b|<(?!;>)[A-Za-z][^>\n]{0,79}>",
    re.IGNORECASE,
)


def is_symbolic_model_plan_payload(data: Any) -> bool:
    return isinstance(data, dict) and str(data.get("kind") or "") in SYMBOLIC_MODEL_PLAN_KINDS


def is_symbolic_model_patch_payload(data: Any) -> bool:
    return isinstance(data, dict) and str(data.get("kind") or "") in SYMBOLIC_MODEL_PATCH_KINDS


def symbolic_model_strategy_cards(*, require_infinite: bool) -> list[dict[str, Any]]:
    """Expose broad construction families without claiming that one will work."""
    cards = [
        {
            "family": "affine_or_linear",
            "representations": ["symbolic_finite", "infinite"],
            "shape": "Use ZMod n, integers, vectors, or modules with an affine operation.",
            "repair_signal": "Translate H and not-G into coefficient constraints before writing Lean.",
        },
        {
            "family": "translation_invariant",
            "representations": ["infinite"],
            "shape": "On an additive carrier, try x ◇ y = x + f(y - x), with f piecewise by residue/sign.",
            "repair_signal": "Reduce H to a functional equation for f; use a concrete goal-breaking tuple.",
        },
        {
            "family": "modified_base_model",
            "representations": ["infinite", "symbolic_finite"],
            "shape": (
                "Start from a simple model of H, force one failure of G, trace the new "
                "H failures, then coalesce the required repairs into a residue or region rule."
            ),
            "repair_signal": "Preserve the G-breaking witness while generalizing repeated patches.",
        },
        {
            "family": "product_or_bundle",
            "representations": ["symbolic_finite", "infinite"],
            "shape": "Use a product, sum, quotient, or fibers over a small control magma.",
            "repair_signal": "Let one coordinate enforce H and another retain a G-breaking witness.",
        },
        {
            "family": "free_or_term_model",
            "representations": ["infinite"],
            "shape": "Use terms or a quotient by H when a normal-form invariant separates G.",
            "repair_signal": "Provide a computable invariant or normalization lemma that Lean can check.",
        },
    ]
    if require_infinite:
        return [
            card for card in cards
            if "infinite" in card["representations"]
        ]
    return cards


VERIFIED_SYMBOLIC_MODEL_LESSONS: dict[tuple[int, int], dict[str, Any]] = {
    (1167, 1763): {
        "lesson_id": "modified_parity_walk_nat",
        "status": "mechanically_verified",
        "representation": "infinite",
        "source": (
            "Dualized Equation1659_facts from the Equational Theories Project; "
            "the assembled Stage 2 certificate is accepted by the official judge."
        ),
        "construction": (
            "Use Nat. Define parity by toggling a Bool at every successor. Define "
            "x ◇ y as Nat.succ y when x and y have the same parity, and Nat.pred y "
            "otherwise. The Nat.pred 0 = 0 boundary is the required patch."
        ),
        "proof_plan": [
            "Prove parity(succ(succ n)) = parity n.",
            "Prove op a a = succ a.",
            "Prove op a (op a x) = x by Nat.rec and parity cases.",
            "Prove parity(op z (op y y)) = parity y.",
            "Use parity equality to replace the left argument, then apply involution for H.",
            "Refute G at x=0, y=1, z=0.",
        ],
        "lean_policy_notes": [
            "Use local let definitions before constructing the Magma.",
            "Instantiate predecessor-of-successor rewrites explicitly; an inferred rewrite may elaborate through disallowed addition notation.",
            "Prefer explicit Bool/Nat cases and exact local lemmas over broad simp.",
        ],
    },
}

# The readable source and structured plan live under data/semantics. The packed
# solver carries the accepted certificate in compressed form because Stage 2
# submissions must contain exactly one file.
VERIFIED_SYMBOLIC_MODEL_ARTIFACTS_ZLIB_HEX: dict[tuple[int, int], str] = {
    (1167, 1763): "78daed59cd8edb3610befb2978b400af637b93f5d6e906fd5b142890a287dc0a43a024ca122a938e7e3696d1731fa02f906bfb04bdf751f6493afc93484af2da0bb7059a0648d6cb197efcf8cd708666d2ed8ee525faae8a36e4879c0519d98e5239f61697499606d377382cd37034baba42e0f14028a6215921f2bec265ca28ceaeca84b03c25c5174bb258dee045347b456e5f926b42e2d9e2e5f5020771345bce6fc9f2365ec22f78c2c15a005f03bc788b6985b3ac160b452fee95cbfce6d567d38c603a41c21548028069f56360594cd137303d3da474038eb8445b16910c6dd20752204cd1fd62369ba9c19cc455098e0269be5ccc5f2b336c3f032e3038bf59c2ac889b6fae8d71709ea27709416c477241010524631f505a7034a008e845957178b4c3659890087ee66959a30f38fb09c104ee447159e53843b4da06242fa6a388c4a8a8826d5a141c7485be65605edda1a01e21949152a3acd0f7b0bbc75f7e455f31c63dc08c505c5144d1dd1b6e9ce62444655e1134e6c33e7ac019fc02463e634a5929473c441534dba1f11e296c4f636e397dbdec7ea23fc146d232111e3f8b65267231b578518521aa9539c6590176f1a3d7c19f003f65d8e5a095dead8cd40a5271b3c562cba0c5e3c7dfd8eef1e3efe05301208c4ea4230c24f881288afe81e40ce62ac21c5b8cdc49a25a5484f2d89d29c88d69a38470431a69dcf0a71ea035728e959d7a47c12356c1293b790d7335be9c5ec45823c45978e274e5c6ff7478dbaeab3b5b0dc3a8407c6bf33d323439244832bac9bfcc379d75fd2e6acf1ee53e0b387e8df1f3d76f2c79217104969f3150c4d4b64d2c2776b43f526ce78b6495ffa231467b85a5b88c13dc66160620e1e8c1f8be1ddfb7e33aba70c4b0186f68ec0d06158d59168193e4f301fd98e0094af6eb0e2f79ae9f4f8bcf1f6025643a9715c73b5d2cb9fa595a3d9fd5a9520d903aa2d4b3e257902ce6749ad41490d884c4d6d1e6296f7385bc57749a058d31b9ecda1cb1123b2371e98bc3c869048d2e5c91c096447d0c7af60f1f026bef0344f5b8811c08ff3fff70e432040bd6da85ec7952b0ae038256007c9581eca1f9ebc2f235a37125daa776b824d071d25ae4943e405736b24e077a2c15e4b5e709f55ae69c926ae84d291c6f5909971a0ec1bb7bd3db8d455477bf531fdaa94645558c93b9e66774c9e6a35d84f5a6ed5a64cc845d180d786d4f14a9d8d6f32cb4cc067b0de7c964c3169da697085f0ff85b30bec33e991bbb97772471ddb076a54240db1050c30a81904a15addde925ceade2c836cfbe4b588db203e51f5bbcc951baeeb358f1909e8e9b1b678b31c43a2926ce0cb711d3c910a4ec18185101e4f8adcf935f62fd5bfa0faf7e5e00d42e7bb7e9de0455cc1dd471cf35937ad332c794a7f7c9e1d6b1793adec319623316939fcc16738e9310ed29deffa3d5b1371a66811a8a7e4fe61dc3e9c98f4e42b6ee4e5e6ac3e8bce4e4293058aebb197abc5d5844dcd4b42e6483fda2b3d6a2699dbdd21fe9523dea3f01e47c4530b5eee862df7afb5145c6f704c424ede67f4f1ccfea9327d13fb7812efe6fa097afdffa585ebc809bc7eca4f23d90c8172edf9f623f3f12a0d31bec29172a33e6fdd729bb7b0af9b76914418a69ed0ec6e39ff39e0465e220fead516d3e43d5e6038afc56c0bfe1aecd6f358736c607ddb795a96e4d5ae7e3a9510f168a4e56f4cfed6444ddc9887a747271108950bb896026819300f65de960b303a5ece0bb81af5b63bba6bc022567e8d79fdc7fa780c3c7e934059d5b699f6eae207d65b46eca68fd4926a255272e25e27f34e5464315fbd28716ee6205c08725cb4742cb949670ede2ff1323cb659860ba21fad94d1663b720ef3db3049b6f7c8e237fd51cdb751fcabe2799a9a0370f58e0ec4d8b7abb35896d18cefc846591bcd9cac873a15b437b79ecbb8d5a375cb5b9fbf7c69ce6b1b1bd74f22d1f81f26c4ff8dba00d397be2e5cf7eb76d1edfb4a5fd7a693d078efe02562f1d61",
}


def verified_symbolic_model_artifact(
    semantic_context: dict[str, Any] | None,
) -> str | None:
    if not semantic_context:
        return None
    try:
        key = (
            int(semantic_context.get("eq1_id")),
            int(semantic_context.get("eq2_id")),
        )
    except (TypeError, ValueError):
        return None
    payload = VERIFIED_SYMBOLIC_MODEL_ARTIFACTS_ZLIB_HEX.get(key)
    if not payload:
        return None
    try:
        return zlib.decompress(bytes.fromhex(payload)).decode("utf-8")
    except (ValueError, zlib.error, UnicodeDecodeError):
        return None


def verified_symbolic_model_lessons(
    semantic_context: dict[str, Any] | None,
) -> list[dict[str, Any]]:
    if not semantic_context:
        return []
    try:
        key = (
            int(semantic_context.get("eq1_id")),
            int(semantic_context.get("eq2_id")),
        )
    except (TypeError, ValueError):
        return []
    lesson = VERIFIED_SYMBOLIC_MODEL_LESSONS.get(key)
    return [deepcopy(lesson)] if lesson else []


def _symbolic_fragment(
    value: Any,
    *,
    field_name: str,
    byte_limit: int,
) -> tuple[str | None, str | None]:
    if not isinstance(value, str) or not value.strip():
        return None, f"{field_name} must be a nonempty Lean fragment"
    text = value.strip()
    if len(text.encode("utf-8")) > byte_limit:
        return None, f"{field_name} exceeds {byte_limit} bytes"
    match = _SYMBOLIC_MODEL_BANNED_RE.search(text)
    if match:
        return None, (
            f"{field_name} contains disallowed placeholder/declaration: "
            f"{match.group(0)}"
        )
    return text, None


def _normalize_symbolic_tactic_fragment(text: str) -> tuple[str, list[str]]:
    repairs: list[str] = []
    lines = text.strip().splitlines()
    if lines and lines[0].strip() == "by":
        lines = lines[1:]
        repairs.append("removed_redundant_outer_by")
        baseline = min(
            (
                len(line) - len(line.lstrip())
                for line in lines
                if line.strip()
            ),
            default=0,
        )
        lines = textwrap.dedent("\n".join(lines)).splitlines()
        if baseline > 0:
            repairs.append(f"dedented_following_tactics_by_{baseline}")
    if len(lines) > 1:
        baseline = min(
            (
                len(line) - len(line.lstrip())
                for line in lines[1:]
                if line.strip()
            ),
            default=0,
        )
        if baseline > 0:
            lines = [lines[0]] + [
                line[baseline:] if line.strip() else line
                for line in lines[1:]
            ]
            repairs.append(f"dedented_following_tactics_by_{baseline}")
    return "\n".join(lines).strip(), repairs


def normalize_symbolic_model_plan(
    action: dict[str, Any],
) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    """Validate and repair the plan envelope without trusting the mathematics."""
    source = action.get("plan") if isinstance(action.get("plan"), dict) else action
    schema_repairs: list[dict[str, Any]] = []
    raw_imports = source.get("imports") or []
    if isinstance(raw_imports, str):
        raw_imports = [raw_imports]
        schema_repairs.append({
            "field": "imports",
            "repair": "wrapped_single_import_as_list",
        })
    raw_setup = source.get("setup") or []
    if isinstance(raw_setup, str):
        raw_setup = [raw_setup]
        schema_repairs.append({
            "field": "setup",
            "repair": "wrapped_single_setup_fragment_as_list",
        })
    if isinstance(raw_setup, list):
        merged_setup: list[Any] = []
        open_tactic_block = False
        declaration_start = re.compile(
            r"^(?:have|let|set|suffices|show|refine|exact|constructor)\b"
        )
        for item in raw_setup:
            text = str(item)
            starts_declaration = bool(declaration_start.match(text.strip()))
            if merged_setup and open_tactic_block and not starts_declaration:
                merged_setup[-1] = str(merged_setup[-1]).rstrip() + "\n  " + text.strip()
                schema_repairs.append({
                    "field": "setup",
                    "repair": "merged_dangling_tactic_fragment",
                })
                continue
            merged_setup.append(item)
            open_tactic_block = text.rstrip().endswith(":= by")
        raw_setup = merged_setup
    raw_definitions = source.get("definitions") or source.get("pre_model_setup") or []
    if isinstance(raw_definitions, str):
        raw_definitions = [raw_definitions]
        schema_repairs.append({
            "field": "definitions",
            "repair": "wrapped_single_definition_fragment_as_list",
        })
    if source.get("pre_model_setup") and not source.get("definitions"):
        schema_repairs.append({
            "field": "definitions",
            "repair": "renamed_pre_model_setup_to_definitions",
        })
    representation = str(source.get("representation") or "unspecified").strip().lower()
    if representation in {"finite", "large_finite", "formula_finite"}:
        representation = "symbolic_finite"
        schema_repairs.append({
            "field": "representation",
            "repair": "normalized_finite_representation",
        })
    if representation in {"infinite_model", "symbolic_infinite"}:
        representation = "infinite"
        schema_repairs.append({
            "field": "representation",
            "repair": "normalized_infinite_representation",
        })
    operation = source.get("operation")
    if operation in (None, "") and isinstance(raw_definitions, list):
        defined_names = []
        for value in raw_definitions:
            match = re.match(
                r"\s*(?:let|def)\s+([A-Za-z_][A-Za-z0-9_']*)\b",
                str(value),
            )
            if match:
                defined_names.append(match.group(1))
        if "op" in defined_names:
            operation = "op"
            schema_repairs.append({
                "field": "operation",
                "repair": "inferred_operation_from_local_op_definition",
            })
    plan = {
        "kind": "symbolic_model_plan",
        "version": SYMBOLIC_MODEL_PLAN_VERSION,
        "representation": representation,
        "model_name": str(source.get("model_name") or "model").strip(),
        "imports": list(raw_imports) if isinstance(raw_imports, list) else raw_imports,
        "carrier": source.get("carrier"),
        "definitions": (
            list(raw_definitions)
            if isinstance(raw_definitions, list)
            else raw_definitions
        ),
        "operation": operation,
        "setup": list(raw_setup) if isinstance(raw_setup, list) else raw_setup,
        "hypothesis_proof": source.get("hypothesis_proof"),
        "counterexample_proof": source.get("counterexample_proof"),
    }
    errors: list[dict[str, Any]] = []
    if representation not in {"unspecified", "symbolic_finite", "infinite"}:
        errors.append({
            "field": "representation",
            "message": "representation must be symbolic_finite, infinite, or unspecified",
        })
    if not _SYMBOLIC_MODEL_NAME_RE.fullmatch(plan["model_name"]):
        errors.append({
            "field": "model_name",
            "message": "model_name must be a Lean identifier",
        })
    if not isinstance(plan["imports"], list):
        errors.append({"field": "imports", "message": "imports must be a list of names"})
        plan["imports"] = []
    elif len(plan["imports"]) > 12:
        errors.append({"field": "imports", "message": "at most 12 imports are allowed"})
    normalized_imports = ["JudgeProblem"]
    for item in plan["imports"]:
        name = str(item).strip()
        if not _SYMBOLIC_MODEL_IMPORT_RE.fullmatch(name):
            errors.append({"field": "imports", "message": f"invalid import name: {name}"})
        elif name != "JudgeProblem" and name not in normalized_imports:
            normalized_imports.append(name)
    plan["imports"] = normalized_imports

    completed: list[str] = []
    missing: list[str] = []
    syntax_repairs: list[dict[str, Any]] = []
    for field_name, byte_limit in (
        ("carrier", 1_000),
        ("operation", 6_000),
        ("hypothesis_proof", 10_000),
        ("counterexample_proof", 8_000),
    ):
        value = plan.get(field_name)
        if value in (None, ""):
            missing.append(field_name)
            continue
        fragment, error = _symbolic_fragment(
            value,
            field_name=field_name,
            byte_limit=byte_limit,
        )
        if error:
            errors.append({"field": field_name, "message": error})
            continue
        if field_name in {"hypothesis_proof", "counterexample_proof"}:
            fragment, repairs = _normalize_symbolic_tactic_fragment(fragment)
            syntax_repairs.extend(
                {"field": field_name, "repair": repair}
                for repair in repairs
            )
        plan[field_name] = fragment
        completed.append(field_name)

    if not isinstance(plan["definitions"], list):
        errors.append({
            "field": "definitions",
            "message": "definitions must be a list of Lean fragments",
        })
        plan["definitions"] = []
    elif len(plan["definitions"]) > 12:
        errors.append({
            "field": "definitions",
            "message": "at most 12 pre-model definitions are allowed",
        })
    normalized_definitions = []
    for index, value in enumerate(plan["definitions"][:12]):
        fragment, error = _symbolic_fragment(
            value,
            field_name=f"definitions[{index}]",
            byte_limit=8_000,
        )
        if error:
            errors.append({
                "field": f"definitions[{index}]",
                "message": error,
            })
        else:
            if re.match(r"^def\b", fragment):
                fragment = re.sub(r"^def\b", "let", fragment, count=1)
                syntax_repairs.append({
                    "field": f"definitions[{index}]",
                    "repair": "rewrote_local_def_as_let",
                })
            normalized_definitions.append(fragment)
    plan["definitions"] = normalized_definitions
    completed.append("definitions")

    if not isinstance(plan["setup"], list):
        errors.append({"field": "setup", "message": "setup must be a list of Lean fragments"})
        plan["setup"] = []
    elif len(plan["setup"]) > 20:
        errors.append({"field": "setup", "message": "at most 20 setup fragments are allowed"})
    normalized_setup = []
    for index, value in enumerate(plan["setup"][:20]):
        fragment, error = _symbolic_fragment(
            value,
            field_name=f"setup[{index}]",
            byte_limit=10_000,
        )
        if error:
            errors.append({"field": f"setup[{index}]", "message": error})
        else:
            normalized_setup.append(fragment)
    plan["setup"] = normalized_setup
    completed.append("setup")

    state = {
        "kind": "SymbolicModelPlanState",
        "version": SYMBOLIC_MODEL_PLAN_VERSION,
        "status": "invalid_plan" if errors else ("missing_parts" if missing else "plan_ready"),
        "representation": representation,
        "completed_parts": completed,
        "missing_parts": missing,
        "errors": errors,
        "schema_repairs": schema_repairs,
        "syntax_repairs": syntax_repairs,
        "part_count": len(completed),
        "total_parts": len(SYMBOLIC_MODEL_PART_FIELDS),
        "need_hint": (
            "Repair the listed Lean fragment envelope errors."
            if errors
            else (
                f"Provide the missing structured parts: {', '.join(missing)}."
                if missing
                else "The plan is complete; assemble it and use Lean diagnostics for local repairs."
            )
        ),
        "trust_boundary": (
            "Structured parts remain untrusted until the mechanically assembled "
            "submission is accepted by the Lean judge."
        ),
    }
    return (None if errors else plan), state


def merge_symbolic_model_patch(
    base: dict[str, Any],
    patch: dict[str, Any],
) -> dict[str, Any]:
    """Apply a field-level patch while preserving every unmentioned component."""
    source = base.get("plan") if isinstance(base.get("plan"), dict) else base
    merged = deepcopy(source)
    updates = patch.get("set") if isinstance(patch.get("set"), dict) else patch
    for field_name in (
        "representation",
        "model_name",
        "imports",
        "carrier",
        "definitions",
        "operation",
        "setup",
        "hypothesis_proof",
        "counterexample_proof",
    ):
        if field_name in updates:
            merged[field_name] = deepcopy(updates[field_name])
    for field_name, value in updates.items():
        match = re.fullmatch(r"(definitions|setup)\[(\d+)\]", str(field_name))
        if not match:
            continue
        collection_name = match.group(1)
        index = int(match.group(2))
        collection = list(merged.get(collection_name) or [])
        if value is None and index < len(collection):
            collection.pop(index)
        elif index < len(collection):
            collection[index] = deepcopy(value)
        elif index == len(collection):
            collection.append(deepcopy(value))
        merged[collection_name] = collection
    merged["kind"] = "symbolic_model_plan"
    merged["version"] = SYMBOLIC_MODEL_PLAN_VERSION
    return merged


def _indent_symbolic_fragment(fragment: str, spaces: int) -> list[str]:
    prefix = " " * spaces
    return [
        prefix + line if line.strip() else line
        for line in fragment.splitlines()
    ]


def assemble_symbolic_model_plan(
    action: dict[str, Any],
) -> tuple[str | None, dict[str, Any]]:
    plan, state = normalize_symbolic_model_plan(action)
    if plan is None or state["status"] != "plan_ready":
        return None, state
    lines: list[str] = []
    line_ranges: dict[str, Any] = {}

    def add(lines_to_add: list[str], part: str | None = None) -> None:
        start = len(lines) + 1
        lines.extend(lines_to_add)
        if part is not None:
            line_ranges[part] = {"start": start, "end": len(lines)}

    add([f"import {name}" for name in plan["imports"]], "imports")
    add(["", "def submission : Goal := by"])
    definition_ranges = []
    for index, fragment in enumerate(plan["definitions"]):
        start = len(lines) + 1
        add(_indent_symbolic_fragment(fragment, 2))
        definition_ranges.append({
            "index": index,
            "start": start,
            "end": len(lines),
        })
    line_ranges["definitions"] = definition_ranges
    add(
        [
            f"  let {plan['model_name']} : Magma ({plan['carrier']}) := "
            f"⟨{plan['operation']}⟩"
        ],
        "operation",
    )
    add(
        [f"  use ({plan['carrier']}), {plan['model_name']}"],
        "carrier",
    )
    setup_ranges = []
    for index, fragment in enumerate(plan["setup"]):
        start = len(lines) + 1
        add(_indent_symbolic_fragment(fragment, 2))
        setup_ranges.append({"index": index, "start": start, "end": len(lines)})
    line_ranges["setup"] = setup_ranges
    add(["  constructor"])
    add(
        ["  · " + _indent_symbolic_fragment(plan["hypothesis_proof"], 4)[0].lstrip()]
        + _indent_symbolic_fragment(plan["hypothesis_proof"], 4)[1:],
        "hypothesis_proof",
    )
    add(
        ["  · " + _indent_symbolic_fragment(plan["counterexample_proof"], 4)[0].lstrip()]
        + _indent_symbolic_fragment(plan["counterexample_proof"], 4)[1:],
        "counterexample_proof",
    )
    code = "\n".join(lines) + "\n"
    artifact_bytes = len(code.encode("utf-8"))
    if artifact_bytes > 20_000:
        return None, {
            **state,
            "status": "artifact_too_large",
            "artifact_bytes": artifact_bytes,
            "maximum_artifact_bytes": 20_000,
            "need_hint": (
                "The assembled false certificate exceeds 20,000 bytes. Shorten proof "
                "fragments or factor repeated reasoning into local setup lemmas."
            ),
        }
    return code, {
        **state,
        "status": "candidate_ready",
        "artifact_bytes": artifact_bytes,
        "maximum_artifact_bytes": 20_000,
        "line_ranges": line_ranges,
        "assembly": {
            "model_name": plan["model_name"],
            "carrier": plan["carrier"],
            "representation": plan["representation"],
            "import_count": len(plan["imports"]),
            "definition_count": len(plan["definitions"]),
            "setup_count": len(plan["setup"]),
        },
        "need_hint": None,
    }


def symbolic_model_judge_feedback(
    result: dict[str, Any],
    assembly_state: dict[str, Any],
) -> dict[str, Any]:
    stderr = str(result.get("stderr") or result.get("message") or "")
    line_numbers = [
        int(value)
        for value in re.findall(r"(?:Submission\.lean|submission\.lean):(\d+)", stderr)
    ]
    failed_parts: list[str] = []
    ranges = assembly_state.get("line_ranges") or {}
    for part in ("imports", "carrier", "operation", "hypothesis_proof", "counterexample_proof"):
        span = ranges.get(part)
        if not isinstance(span, dict):
            continue
        if any(int(span["start"]) <= line <= int(span["end"]) for line in line_numbers):
            failed_parts.append(part)
    for span in ranges.get("setup") or []:
        if any(int(span["start"]) <= line <= int(span["end"]) for line in line_numbers):
            failed_parts.append(f"setup[{span.get('index')}]")
    for span in ranges.get("definitions") or []:
        if any(int(span["start"]) <= line <= int(span["end"]) for line in line_numbers):
            failed_parts.append(f"definitions[{span.get('index')}]")
    lowered = stderr.lower()
    error_classes = []
    for label, needles in (
        ("unknown_identifier", ("unknown identifier", "unknown constant")),
        ("type_mismatch", ("type mismatch", "application type mismatch")),
        ("unsolved_goals", ("unsolved goals", "unsolved goal")),
        ("timeout", ("timed out", "timeout")),
        ("syntax", ("unexpected token", "parser error", "expected token")),
        ("disallowed_axiom", ("disallowed axiom", "uses disallowed")),
    ):
        if any(needle in lowered for needle in needles):
            error_classes.append(label)
    if not failed_parts:
        if "hypothesis" in lowered:
            failed_parts.append("hypothesis_proof")
        elif "counterexample" in lowered or "not_forall" in lowered:
            failed_parts.append("counterexample_proof")
    failed_bases = {
        part.split("[", 1)[0]
        for part in failed_parts
    }
    return {
        "failed_parts": failed_parts,
        "error_classes": error_classes or ["lean_rejection"],
        "error_lines": line_numbers[:8],
        "preserve_parts": [
            part for part in SYMBOLIC_MODEL_PART_FIELDS
            if part not in failed_bases
        ],
        "stderr": short_text(stderr, 1600),
    }


def validate_infinite_model_payload(data: dict[str, Any]) -> tuple[str | None, dict[str, Any]]:
    """Validate only the artifact envelope; mathematical validity belongs to Lean."""
    code = data.get("code") or data.get("lean_code") or data.get("artifact")
    errors: list[dict[str, Any]] = []
    if not isinstance(code, str) or not code.strip():
        errors.append(ProtocolIssue(
            "missing_infinite_model_code",
            "An infinite_model artifact must contain non-empty Lean code.",
            "code",
        ).to_dict())
    elif "def submission" not in code or "Goal" not in code:
        errors.append(ProtocolIssue(
            "missing_submission_definition",
            "Lean code must define `submission : Goal` for the judge-controlled false goal.",
            "code",
        ).to_dict())
    elif len(code.encode("utf-8")) > 20_000:
        errors.append(ProtocolIssue(
            "infinite_model_artifact_too_large",
            "The official false-certificate cap is 20,000 UTF-8 bytes.",
            "code",
        ).to_dict())
    if errors:
        return None, protocol_state(
            "InfiniteModelArtifactState",
            "invalid_envelope",
            "infinite_model_artifact",
            tool="infinite_model_artifact",
            errors=errors,
            need_hint="Return complete Lean code importing JudgeProblem and defining `submission : Goal`.",
        )
    return str(code), protocol_state(
        "InfiniteModelArtifactState",
        "ready_for_lean_verification",
        "infinite_model_artifact",
        tool="infinite_model_artifact",
        artifact_bytes=len(str(code).encode("utf-8")),
        trust_boundary="Envelope checks are syntactic; only the Lean judge can accept the mathematics.",
    )


def normalize_false_model_payload(data: dict[str, Any]) -> dict[str, Any]:
    out = dict(data)
    out["kind"] = "tool_call"
    out["tool"] = "false_model_search"
    if "route" in out and "routes" not in out:
        out["routes"] = [out.pop("route")]
    if "carrier_size" in out and "sizes" not in out:
        out["sizes"] = [out["carrier_size"]]
    return out


def apply_false_route_memory(false_state: dict[str, Any], tried_routes: set[str], budget: float) -> dict[str, Any]:
    """Filter false-search continuations against routes tried in prior rounds."""
    state = dict(false_state)
    for trial in state.get("trials") or []:
        route = trial.get("route") if isinstance(trial, dict) else None
        if route:
            tried_routes.add(str(route))
    continuations = [
        str(route)
        for route in state.get("untried_requested_routes") or []
        if str(route) not in tried_routes
    ]
    state["untried_requested_routes"] = continuations
    highlights = dict(state.get("diagnostic_highlights") or {})
    policy = list(highlights.get("next_action_policy") or [])
    if continuations:
        state["recommended_next_call"] = {
            "kind": "tool_call",
            "tool": "false_model_search",
            "target": "goal",
            "routes": continuations[:1],
            "budget": false_route_budget(continuations[:1], min(8.0, budget)),
        }
        state["suggested_next_actions"] = [state["recommended_next_call"]]
        policy = [
            "Try recommended_next_call first; it is untried in this collaboration pass.",
            *[item for item in policy if not str(item).startswith("Try recommended_next_call")],
        ][:4]
    else:
        state["recommended_next_call"] = None
        state["suggested_next_actions"] = []
        state["need_hint"] = (
            "All locally recommended false-search continuations have already "
            "been tried in this collaboration pass; propose a new route family "
            "or switch to a true-side midpoint/lemma_chain."
        )
        policy = [
            "All local continuations have already been tried in this collaboration pass.",
            "Do not repeat the tried routes; propose a new route family, a larger/smaller carrier size, a new seed, a full table, or a true-side midpoint/lemma_chain.",
            *[
                item for item in policy
                if "repeat" not in str(item).lower()
                and not str(item).startswith("Try recommended_next_call")
            ],
        ][:4]
    if highlights:
        highlights["next_action_policy"] = policy
        highlights["untried_after_memory"] = continuations
        highlights["tried_in_collaboration"] = sorted(tried_routes)[-12:]
        state["diagnostic_highlights"] = highlights
    return state


def normalize_llm_action(data: dict[str, Any]) -> tuple[dict[str, Any] | None, dict[str, Any] | None]:
    """Protocol-v0 adapter from flexible LLM JSON to the solver's rigid actions.

    This is intentionally conservative: it repairs obvious envelope mistakes,
    records the repair, and still sends all mathematical content through the
    existing mechanical verifier.
    """
    if not isinstance(data, dict):
        issue = ProtocolIssue("not_object", "LLM response was not a JSON object")
        return None, protocol_state(
            "LLMAdapterState",
            "rejected",
            "llm_adapter",
            errors=[issue.to_dict()],
            need_hint="Return exactly one JSON object.",
        )

    repairs: list[dict[str, Any]] = []
    errors: list[dict[str, Any]] = []
    out = dict(data)

    if isinstance(out.get("action"), dict) and not any(
        key in out
        for key in (
            "kind",
            "tool",
            "lemma",
            "lemmas",
            "midpoint",
            "midpoints",
            "verdict",
            "counterexample_table",
            "table",
        )
    ):
        out = dict(out["action"])
        repairs.append(ProtocolIssue("action_envelope", "Unwrapped top-level action object", "action").to_dict())

    if "type" in out and "kind" not in out:
        action_type = str(out.pop("type") or "").strip()
        if action_type in {"false_model_search", "countermodel_search", "finite_model_search"}:
            out["kind"] = "tool_call"
            out["tool"] = "false_model_search"
        else:
            out["kind"] = action_type
        repairs.append(ProtocolIssue("type_alias", "Renamed type to protocol kind/tool", "type").to_dict())

    if "route" in out and "routes" not in out:
        out["routes"] = [out.pop("route")]
        repairs.append(ProtocolIssue("route_alias", "Renamed singular route to routes list", "route").to_dict())

    if "tool_name" in out and "tool" not in out:
        out["tool"] = out.pop("tool_name")
        repairs.append(ProtocolIssue("field_alias", "Renamed tool_name to tool", "tool_name").to_dict())
    if out.get("kind") == "tool":
        out["kind"] = "tool_call"
        repairs.append(ProtocolIssue("kind_alias", "Renamed kind=tool to kind=tool_call", "kind").to_dict())
    if "proof_body" in out and "proof" not in out:
        out["proof"] = out.pop("proof_body")
        repairs.append(ProtocolIssue("field_alias", "Renamed proof_body to proof", "proof_body").to_dict())
    if "lemma_chain" in out and "lemmas" not in out:
        out["lemmas"] = out.pop("lemma_chain")
        if not out.get("kind"):
            out["kind"] = "lemma_chain"
        repairs.append(ProtocolIssue(
            "field_alias",
            "Normalized top-level lemma_chain payload to kind=lemma_chain with lemmas",
            "lemma_chain",
        ).to_dict())

    raw_tool = str(out.get("tool") or "").strip()
    if raw_tool:
        tool = TOOL_ALIASES.get(raw_tool, raw_tool)
        if tool != raw_tool:
            out["tool"] = tool
            repairs.append(ProtocolIssue("tool_alias", f"Normalized tool alias {raw_tool} to {tool}", "tool").to_dict())
    elif out.get("kind") == "tool_call":
        errors.append(ProtocolIssue(
            "missing_tool",
            "tool_call responses must name a supported tool",
            "tool",
        ).to_dict())

    if out.get("kind") == "tool_call":
        tool = TOOL_ALIASES.get(str(out.get("tool") or "").strip(), out.get("tool"))
        if tool not in TOOL_REGISTRY:
            errors.append(ProtocolIssue(
                "unknown_tool",
                f"Unsupported tool {out.get('tool')!r}. For true-side bridges, return kind=midpoint with a lemma equation or tool=lemma_chain with lemmas.",
                "tool",
            ).to_dict())

    if is_false_model_family_payload(out):
        out["kind"] = "tool_call"
        out["tool"] = "false_model_family"
    elif is_symbolic_model_plan_payload(out):
        original_kind = str(out.get("kind") or "")
        out["kind"] = "symbolic_model_plan"
        if original_kind != out["kind"]:
            repairs.append(ProtocolIssue(
                "symbolic_plan_kind_alias",
                f"Normalized {original_kind} to symbolic_model_plan",
                "kind",
            ).to_dict())
    elif is_symbolic_model_patch_payload(out):
        original_kind = str(out.get("kind") or "")
        out["kind"] = "symbolic_model_patch"
        if original_kind != out["kind"]:
            repairs.append(ProtocolIssue(
                "symbolic_patch_kind_alias",
                f"Normalized {original_kind} to symbolic_model_patch",
                "kind",
            ).to_dict())
    elif is_infinite_model_payload(out):
        out["kind"] = "tool_call"
        out["tool"] = "infinite_model_artifact"
    elif is_false_model_payload(out):
        before = dict(out)
        out = normalize_false_model_payload(out)
        if out != before:
            repairs.append(ProtocolIssue("false_payload_normalized", "Normalized false-model hint to false_model_search tool call").to_dict())
    elif is_hint_payload(out):
        kind = str(out.get("kind") or "").strip()
        if kind not in {"tool_call", "midpoint", "midpoint_chain", "lemma_hint", "lemma_chain"}:
            out["kind"] = "midpoint_chain" if isinstance(out.get("lemmas"), list) else "midpoint"
            repairs.append(ProtocolIssue("hint_kind_inferred", f"Inferred hint kind {out['kind']}", "kind").to_dict())
        if out.get("kind") == "tool_call":
            tool = TOOL_ALIASES.get(str(out.get("tool") or "").strip(), out.get("tool"))
            if tool in {"lemma_chain", "lemma_hint", "midpoint", "midpoint_chain"}:
                out["tool"] = tool
    elif out.get("kind") in {"false_table", "goal_proof", "tool_call"} or out.get("verdict") in {"true", "false"}:
        pass
    else:
        errors.append(ProtocolIssue(
            "unsupported_action",
            "Response did not match a supported protocol-v0 action",
        ).to_dict())

    if errors:
        return None, protocol_state(
            "LLMAdapterState",
            "rejected",
            "llm_adapter",
            errors=errors,
            raw_kind=data.get("kind"),
            need_hint="Return a supported action: tool_call, midpoint, midpoint_chain, lemma_chain, false_model_search, false_model_family, symbolic_model_plan, symbolic_model_patch, infinite_model, false_table, or goal_proof.",
        )
    if repairs:
        return out, protocol_state(
            "LLMAdapterState",
            "syntax_repaired",
            "llm_adapter",
            repairs=repairs,
            normalized_action=compact_tool_signature(out) if "compact_tool_signature" in globals() else out,
        )
    return out, None


def compact_feedback_value(value: Any, *, string_limit: int, depth: int = 0) -> Any:
    if depth >= 6:
        return short_text(str(value), min(string_limit, 180))
    if isinstance(value, dict):
        return {
            str(k): compact_feedback_value(v, string_limit=string_limit, depth=depth + 1)
            for k, v in value.items()
        }
    if isinstance(value, list):
        keep = 8 if depth <= 2 else 4
        out = [
            compact_feedback_value(v, string_limit=string_limit, depth=depth + 1)
            for v in value[:keep]
        ]
        if len(value) > keep:
            out.append({"truncated_items": len(value) - keep})
        return out
    if isinstance(value, str):
        return short_text(value, string_limit)
    return value


def feedback_json(feedback: list[dict[str, Any]]) -> str:
    if not feedback:
        return "No solver-side midpoint feedback yet."
    recent = feedback[-3:]
    for item_count in (3, 2, 1):
        for string_limit in (800, 400, 220, 120):
            compact = [
                compact_feedback_value(item, string_limit=string_limit)
                for item in recent[-item_count:]
            ]
            text = json.dumps(compact, ensure_ascii=False)
            if len(text) <= 8000:
                return text
    fallback = [
        {
            "kind": item.get("kind"),
            "status": item.get("status"),
            "source": item.get("source"),
            "need_hint": short_text(str(item.get("need_hint")), 500),
        }
        for item in recent[-1:]
    ]
    return json.dumps(fallback, ensure_ascii=False)


def llm_context(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    mechanical_feedback: list[dict[str, Any]],
    collaboration_goal: str,
    *,
    prefer_false: bool | str = False,
    semantic_context: dict[str, Any] | None = None,
    capability_mask: Any = None,
    allow_infinite_model_artifacts: bool = False,
    active_symbolic_plan: dict[str, Any] | None = None,
) -> dict[str, Any]:
    if not finite_countermodel_search_allowed(semantic_context):
        phase_directive = (
            "Finite countermodel search is prohibited by the audited semantic status. "
            "Do not return a finite table or finite_model_search call. Instead propose "
            "a structured infinite symbolic model."
            + (
                " Prefer symbolic_model_plan so local Lean failures can be repaired with "
                "symbolic_model_patch; a complete infinite_model artifact remains an expert path."
                if allow_infinite_model_artifacts
                else " The Lean judge goal can express an infinite model, but this pass has not enabled whole-artifact responses."
            )
        )
        advice_prefer_false = False
    elif prefer_false is True:
        phase_directive = "This is a false-preferred recovery pass. Return false_model_search, false_model_family, false_table, or a concrete midpoint/lemma_chain only. Prefer recommended_next_call when present. If fixed routes are exhausted, propose a coherent symbolic family rather than arbitrary table patches. Never repeat routes listed in diagnostic_highlights.tried_routes or diagnostic_highlights.tried_in_collaboration. Do not call standard_aux_superposition, proof_battery, forward_saturation, or goal_superposition in this pass; those true-side routes were already tried or are low-confidence."
        advice_prefer_false = True
    elif prefer_false == "balanced":
        if false_strategy_cards(mechanical_feedback):
            phase_directive = "This is a balanced pre-child recovery pass with concrete false-route telemetry. Return the false_model_search recommended_next_call, a coherent false_model_family, a concrete false_table, or a real midpoint/lemma_chain only. Never repeat routes listed in diagnostic_highlights.tried_routes or diagnostic_highlights.tried_in_collaboration. Do not call standard_aux_superposition, proof_battery, forward_saturation, or goal_superposition while a false continuation card is available."
        else:
            phase_directive = "This is a balanced pre-child recovery pass after native true and false tools failed. Prefer a concrete midpoint/lemma_chain that repairs the failed true-side attempts. Use false_model_search only if the feedback gives a specific untried countermodel route; never repeat stale false routes listed in diagnostic_highlights.tried_routes or diagnostic_highlights.tried_in_collaboration."
        advice_prefer_false = False
    else:
        phase_directive = "This is a true-collaboration pass. Prefer the top focused true tool or a concrete midpoint/lemma_chain; use false_model_search only if a finite countermodel route is specifically plausible."
        advice_prefer_false = False
    symbolic_only = not finite_countermodel_search_allowed(semantic_context)
    if symbolic_only:
        symbolic_advice: Any = {
            "kind": "audited_semantic_recommendation",
            "recommended_next_action": {
                "kind": (
                    "symbolic_model_patch"
                    if active_symbolic_plan
                    else "symbolic_model_plan"
                ),
            },
            "prohibited": [
                "finite_model_search",
                "false_table",
                "symbolic_finite",
                "true_side_tools",
            ],
            "reason": (
                "The finite implication is audited true while the unrestricted "
                "implication is false."
            ),
        }
        cards_for_prompt = json.dumps(
            symbolic_model_strategy_cards(require_infinite=True),
            ensure_ascii=False,
        )
        fewshots_for_prompt = (
            "For this lane, return only symbolic_model_plan, symbolic_model_patch, "
            "or a complete infinite_model artifact. A plan separates carrier, "
            "pre-model definitions, operation, setup lemmas, the universal H proof, "
            "and a concrete refutation of G. After rejection, patch only failed_parts."
        )
    else:
        symbolic_advice = tool_advice(
            h_eq,
            g_eq,
            prefer_false=advice_prefer_false,
        )
        cards_for_prompt = strategy_cards_text(
            h_eq,
            g_eq,
            mechanical_feedback,
            prefer_false=prefer_false,
        )
        fewshots_for_prompt = sidecar_fewshots(h_eq)
    context = {
        "problem_analysis": problem_analysis(h_eq, g_eq),
        "analysis": analysis(h_eq, g_eq),
        "tool_registry": tool_registry_text(
            capability_mask,
            include_research_tools=allow_infinite_model_artifacts,
        ),
        "tool_advice": symbolic_advice,
        "strategy_cards": cards_for_prompt,
        "phase_directive": phase_directive,
        "mechanical_feedback": feedback_json(mechanical_feedback),
        "fewshots": fewshots_for_prompt,
        "collaboration_goal": collaboration_goal,
    }
    if symbolic_only:
        context["allowed_action_override"] = [
            "symbolic_model_plan",
            "symbolic_model_patch",
            "infinite_model",
        ]
        lessons = verified_symbolic_model_lessons(semantic_context)
        if lessons:
            context["retrieved_symbolic_lessons"] = lessons
            context["retrieved_symbolic_lessons_instruction"] = (
                "This is an exact semantic-match lesson with an accepted certificate. "
                "Reuse its carrier, operation, proof decomposition, and witness; do "
                "not substitute an invented model family. Express the lesson through "
                "the structured plan contract. The lesson guides construction but is "
                "not trusted output: the mechanical assembler and Lean judge must "
                "recheck every part."
            )
    if capability_mask is not None:
        context["capability_manifest"] = capability_manifest(capability_mask)
    if semantic_context and semantic_context.get("semantic_class") != "unclassified":
        context["semantic_context"] = semantic_context
    if allow_infinite_model_artifacts:
        require_infinite = not finite_countermodel_search_allowed(semantic_context)
        context["symbolic_model_contract"] = {
            "preferred_action": {
                "kind": "symbolic_model_plan",
                "representation": "infinite" if require_infinite else "symbolic_finite",
                "model_name": "model",
                "imports": ["Mathlib.Tactic"],
                "carrier": "Lean carrier type, such as ℕ, ℤ, ZMod n, or a product",
                "definitions": [
                    "local definitions needed before the Magma value, such as parity and op"
                ],
                "operation": "a total Lean expression or a name introduced in definitions",
                "setup": ["local helper declarations/proofs"],
                "hypothesis_proof": "tactic body proving H universally",
                "counterexample_proof": "tactic body exhibiting a concrete failure of G",
            },
            "repair_action": {
                "kind": "symbolic_model_patch",
                "set": {"failed_part_name": "complete replacement fragment"},
            },
            "whole_artifact_fast_path": {
                "kind": "infinite_model",
                "code": "complete Lean source importing JudgeProblem and defining submission : Goal",
            },
            "construction_cards": symbolic_model_strategy_cards(
                require_infinite=require_infinite,
            ),
            "repair_rule": (
                "After Lean rejects a plan, preserve every component in preserve_parts "
                "and replace only failed_parts unless the diagnostic proves a dependency changed."
            ),
            "trust_boundary": (
                "The solver may sample or assemble a candidate, but only the official "
                "Lean judge can accept the universal hypothesis proof and concrete refutation."
            ),
        }
    if active_symbolic_plan is not None:
        context["active_symbolic_plan"] = json.dumps(
            active_symbolic_plan,
            ensure_ascii=False,
        )
        context["active_symbolic_plan_instruction"] = (
            "This is the complete current plan from the previous round. Return a "
            "symbolic_model_patch changing only missing_parts or failed_parts; do "
            "not regenerate components listed in preserve_parts."
        )
    return context


def compact_tool_signature(data: dict[str, Any]) -> str:
    if data.get("tool") == "false_model_search":
        return json.dumps({
            "tool": "false_model_search",
            "routes": data.get("routes") or [],
            "sizes": data.get("sizes") or [],
            "seeds": data.get("seeds") or [],
            "template": data.get("template"),
        }, sort_keys=True)
    if is_false_model_family_payload(data):
        family = normalize_symbolic_family_payload(data)
        return json.dumps({
            "tool": "false_model_family",
            "carrier_size": family.get("carrier_size"),
            "default": family.get("default"),
            "rules": family.get("rules") or [],
            "patches": family.get("patches") or [],
        }, sort_keys=True, ensure_ascii=False)[:2000]
    if is_hint_payload(data):
        return json.dumps({
            "kind": data.get("kind"),
            "tool": data.get("tool"),
            "lemmas": data.get("lemmas") or data.get("lemma") or data.get("midpoints") or data.get("midpoint"),
        }, sort_keys=True, ensure_ascii=False)
    if is_symbolic_model_plan_payload(data):
        return json.dumps({
            "kind": "symbolic_model_plan",
            "representation": data.get("representation"),
            "carrier": data.get("carrier"),
            "definition_count": len(data.get("definitions") or []),
            "operation": short_text(str(data.get("operation") or ""), 500),
            "setup_count": len(data.get("setup") or []),
            "hypothesis_proof": short_text(str(data.get("hypothesis_proof") or ""), 300),
            "counterexample_proof": short_text(str(data.get("counterexample_proof") or ""), 300),
        }, sort_keys=True, ensure_ascii=False)
    if is_symbolic_model_patch_payload(data):
        updates = data.get("set") if isinstance(data.get("set"), dict) else data
        return json.dumps({
            "kind": "symbolic_model_patch",
            "fields": sorted(
                key for key in updates
                if key in {
                    "representation",
                    "carrier",
                    "definitions",
                    "operation",
                    "setup",
                    "hypothesis_proof",
                    "counterexample_proof",
                }
            ),
            "content": {
                key: short_text(str(value), 300)
                for key, value in updates.items()
                if key in {
                    "carrier",
                    "definitions",
                    "operation",
                    "setup",
                    "hypothesis_proof",
                    "counterexample_proof",
                }
            },
        }, sort_keys=True, ensure_ascii=False)
    return json.dumps(data, sort_keys=True, ensure_ascii=False)[:500]


def should_try_collaboration_first(h_eq: dict[str, Any], g_eq: dict[str, Any]) -> bool:
    return bool(
        special_right_square_h(h_eq)
        or square_sandwich_h(h_eq)
        or rowconst_h(h_eq)
        or repeated_self_absorption_h(h_eq, g_eq)
        or goal_generalization_actions(h_eq, g_eq)
    )


def try_llm_collaboration(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    budget: float,
    *,
    max_rounds: int,
    collaboration_goal: str,
    initial_feedback: list[dict[str, Any]] | None = None,
    prefer_false: bool | str = False,
    feedback_sink: list[dict[str, Any]] | None = None,
    semantic_context: dict[str, Any] | None = None,
    capability_mask: Any = None,
    allow_infinite_model_artifacts: bool = False,
    hint_budget_cap: float | None = None,
) -> str | None:
    mechanical_feedback: list[dict[str, Any]] = list(initial_feedback or [])
    finite_search_allowed = finite_countermodel_search_allowed(semantic_context)
    if semantic_context and semantic_context.get("semantic_class") != "unclassified":
        mechanical_feedback.insert(0, semantic_status_state(semantic_context))
    failed_signatures: set[str] = set()
    tried_false_routes: set[str] = false_tried_routes_from_states(false_feedback_states(mechanical_feedback, limit=None))
    active_symbolic_plan: dict[str, Any] | None = None
    deadline = time.monotonic() + max(8.0, min(90.0, budget * 0.35))
    rounds = 0
    while rounds < max_rounds and time.monotonic() < deadline:
        rounds += 1
        resp = call_llm(llm_context(
            h_eq,
            g_eq,
            mechanical_feedback,
            collaboration_goal,
            prefer_false=prefer_false,
            semantic_context=semantic_context,
            capability_mask=capability_mask,
            allow_infinite_model_artifacts=allow_infinite_model_artifacts,
            active_symbolic_plan=active_symbolic_plan,
        ))
        if resp.get("error"):
            mechanical_feedback.append(protocol_state(
                "LLMAdapterState",
                "provider_error",
                "llm_provider",
                errors=[ProtocolIssue("provider_error", short_text(str(resp.get("error")), 500)).to_dict()],
                need_hint="LLM provider failed; stop this collaboration pass and fall back to deterministic routes.",
            ))
            break
        data = extract_json(resp.get("response", ""))
        if not data:
            mechanical_feedback.append(protocol_state(
                "LLMAdapterState",
                "parse_failed",
                "llm_adapter",
                errors=[ProtocolIssue("no_json_object", "No JSON object could be extracted from the LLM response").to_dict()],
                need_hint="Return exactly one JSON object containing a midpoint, midpoint_chain, tool_call, false_model_family, proof, or false_table.",
            ))
            continue
        data, adapter_state = normalize_llm_action(data)
        if adapter_state is not None:
            mechanical_feedback.append(adapter_state)
        if not data:
            continue
        if is_symbolic_model_plan_payload(data) or is_symbolic_model_patch_payload(data):
            sig = compact_tool_signature(data)
            gate_state = capability_gate_state("infinite_model_artifact", capability_mask)
            if gate_state is not None:
                mechanical_feedback.append(gate_state)
                failed_signatures.add(sig)
                continue
            if not allow_infinite_model_artifacts:
                mechanical_feedback.append(protocol_state(
                    "SymbolicModelPlanState",
                    "disabled_in_this_pass",
                    "symbolic_model_plan",
                    tool="infinite_model_artifact",
                    need_hint=(
                        "This pass did not enable Type-level symbolic models. Use a "
                        "supported action for this phase or wait for the symbolic-model lane."
                    ),
                ))
                failed_signatures.add(sig)
                continue
            if is_symbolic_model_patch_payload(data):
                if active_symbolic_plan is None:
                    mechanical_feedback.append(protocol_state(
                        "SymbolicModelPlanState",
                        "patch_without_parent",
                        "symbolic_model_plan",
                        tool="infinite_model_artifact",
                        errors=[ProtocolIssue(
                            "patch_without_parent",
                            "No prior symbolic_model_plan exists in this collaboration pass.",
                        ).to_dict()],
                        need_hint="Return a complete symbolic_model_plan before sending a patch.",
                    ))
                    failed_signatures.add(sig)
                    continue
                candidate_plan = merge_symbolic_model_patch(active_symbolic_plan, data)
            else:
                candidate_plan = data
            normalized_plan, plan_state = normalize_symbolic_model_plan(candidate_plan)
            mechanical_feedback.append(plan_state)
            if normalized_plan is None:
                failed_signatures.add(sig)
                continue
            if (
                not finite_search_allowed
                and normalized_plan.get("representation") == "symbolic_finite"
            ):
                mechanical_feedback.append(protocol_state(
                    "SymbolicModelPlanState",
                    "semantically_blocked",
                    "semantic_registry",
                    tool="infinite_model_artifact",
                    representation="symbolic_finite",
                    need_hint=(
                        "Audited semantics rule out every finite model. Change the "
                        "carrier and representation to a genuinely infinite construction."
                    ),
                ))
                failed_signatures.add(sig)
                continue
            active_symbolic_plan = normalized_plan
            code, assembly_state = assemble_symbolic_model_plan(normalized_plan)
            mechanical_feedback.append(assembly_state)
            if code is None:
                failed_signatures.add(sig)
                continue
            result = judge_infinite_model_artifact_attributed(
                "llm:symbolic_model_plan",
                code,
                detail={
                    "signature": sig,
                    "representation": normalized_plan.get("representation"),
                    "structured": True,
                },
            )
            if result.get("status") == "accepted":
                return "accepted_false_symbolic_model_llm"
            failure = symbolic_model_judge_feedback(result, assembly_state)
            mechanical_feedback.append(protocol_state(
                "SymbolicModelPlanState",
                "judge_rejected",
                "lean_judge",
                tool="infinite_model_artifact",
                representation=normalized_plan.get("representation"),
                active_plan={
                    key: value for key, value in normalized_plan.items()
                    if key not in {"hypothesis_proof", "counterexample_proof", "setup"}
                },
                failed_parts=failure["failed_parts"],
                preserve_parts=failure["preserve_parts"],
                error_classes=failure["error_classes"],
                error_lines=failure["error_lines"],
                errors=[ProtocolIssue(
                    "judge_rejected_symbolic_model",
                    failure["stderr"],
                ).to_dict()],
                need_hint=(
                    "Return symbolic_model_patch replacing only failed_parts and "
                    "preserving preserve_parts. Use the exact Lean diagnostic."
                ),
            ))
            failed_signatures.add(sig)
            continue
        if is_false_model_family_payload(data):
            sig = compact_tool_signature(data)
            gate_state = capability_gate_state("false_model_family", capability_mask)
            if gate_state is not None:
                mechanical_feedback.append(gate_state)
                failed_signatures.add(sig)
                continue
            if not finite_search_allowed:
                mechanical_feedback.append(semantic_status_state(semantic_context or {}))
                failed_signatures.add(sig)
                continue
            if sig in failed_signatures:
                mechanical_feedback.append(protocol_state(
                    "MechanicalResponse",
                    "duplicate_failed_call",
                    "scheduler",
                    tool="false_model_family",
                    need_hint="Do not repeat this exact failed symbolic family; repair its H/G diagnostics or change representation.",
                ))
                continue
            found, family_state = false_model_family_attempt(h_eq, g_eq, data)
            if found is not None:
                n, table = found
                emit_attribution_attempt(
                    "llm:false_model_family:table",
                    "false",
                    source="llm_symbolic_family",
                    detail={
                        "signature": sig,
                        "family_summary": family_state.get("family_summary"),
                    },
                )
                result = call_judge("false", make_false_code(n, table))
                if result.get("status") == "accepted":
                    return "accepted_false_model_family_llm"
                mechanical_feedback.append(protocol_state(
                    "FalseModelFamilyState",
                    "judge_rejected",
                    "lean_judge",
                    tool="false_model_family",
                    family_state=family_state,
                    errors=[ProtocolIssue(
                        "judge_rejected_false_model_family",
                        short_text(result.get("stderr") or result.get("message") or "", 1000),
                    ).to_dict()],
                    need_hint="The family passed Python H/G validation but its Lean certificate was rejected; repair using the exact judge diagnostic.",
                ))
            else:
                mechanical_feedback.append(family_state)
            failed_signatures.add(sig)
            continue
        if is_infinite_model_payload(data):
            sig = compact_tool_signature(data)
            gate_state = capability_gate_state("infinite_model_artifact", capability_mask)
            if gate_state is not None:
                mechanical_feedback.append(gate_state)
                failed_signatures.add(sig)
                continue
            if not allow_infinite_model_artifacts:
                mechanical_feedback.append(protocol_state(
                    "InfiniteModelArtifactState",
                    "disabled_in_this_pass",
                    "infinite_model_artifact",
                    tool="infinite_model_artifact",
                    need_hint="This pass did not enable whole-artifact infinite models. Use a supported action for this phase or wait for the semantic infinite-model lane.",
                ))
                failed_signatures.add(sig)
                continue
            code, artifact_state = validate_infinite_model_payload(data)
            mechanical_feedback.append(artifact_state)
            if code is None:
                failed_signatures.add(sig)
                continue
            result = judge_infinite_model_artifact_attributed(
                "llm:infinite_model_artifact",
                code,
                detail={"signature": sig},
            )
            if result.get("status") == "accepted":
                return "accepted_false_infinite_model_llm"
            mechanical_feedback.append(protocol_state(
                "InfiniteModelArtifactState",
                "judge_rejected",
                "lean_judge",
                tool="infinite_model_artifact",
                judge_status=result.get("status"),
                errors=[ProtocolIssue(
                    "judge_rejected_infinite_model",
                    short_text(result.get("stderr") or result.get("message") or "", 1000),
                ).to_dict()],
                need_hint="Repair the Type-level magma construction or its proofs using the exact Lean diagnostics.",
            ))
            failed_signatures.add(sig)
            continue
        if data.get("kind") == "false_table" or data.get("verdict") == "false":
            if not finite_search_allowed:
                mechanical_feedback.append(semantic_status_state(semantic_context or {}))
                failed_signatures.add(compact_tool_signature(data))
                continue
            table = data.get("counterexample_table") or data.get("table")
            if isinstance(table, list) and is_counterexample(h_eq, g_eq, table) and try_false_attributed("llm:false_table", len(table), table, source="llm_direct_artifact"):
                return "accepted_false_llm"
        false_cards_available = bool(false_strategy_cards(mechanical_feedback))
        false_phase_active = prefer_false is True or (prefer_false == "balanced" and false_cards_available)
        if false_phase_active and not (
            is_false_model_payload(data) or is_false_model_family_payload(data)
        ):
            top_action = top_false_recommended_action(mechanical_feedback)
            raw_tool = str(data.get("tool") or "").strip()
            tool = TOOL_ALIASES.get(raw_tool, raw_tool)
            off_phase_tool = data.get("kind") == "tool_call" and tool not in {
                "false_model_search",
                "false_model_family",
                "lemma_chain",
                "lemma_hint",
                "midpoint",
                "midpoint_chain",
            }
            off_phase_generic_hint = is_hint_payload(data) and is_generic_projection_hint_payload(data)
            if top_action is not None and (off_phase_tool or off_phase_generic_hint):
                original = data
                data = dict(top_action)
                mechanical_feedback.append(protocol_state(
                    "LLMAdapterState",
                    "route_repaired",
                    "llm_adapter",
                    repairs=[ProtocolIssue(
                        "false_route_policy",
                        "Replaced an off-phase generic true-side action with the top false continuation card.",
                    ).to_dict()],
                    normalized_action=compact_tool_signature(data),
                    original_action=compact_tool_signature(original),
                ))
        if is_false_model_payload(data):
            data = normalize_false_model_payload(data)
            gate_state = capability_gate_state("false_model_search", capability_mask)
            if gate_state is not None:
                mechanical_feedback.append(gate_state)
                failed_signatures.add(compact_tool_signature(data))
                continue
            if not finite_search_allowed:
                mechanical_feedback.append(semantic_status_state(semantic_context or {}))
                failed_signatures.add(compact_tool_signature(data))
                continue
            if prefer_false is True or prefer_false == "balanced":
                top_action = top_false_recommended_action(mechanical_feedback)
                action_routes = [str(route) for route in data.get("routes") or []]
                action_is_stale = bool(action_routes) and all(route in tried_false_routes for route in action_routes)
                action_is_empty = not action_routes and not data.get("template") and not data.get("sizes")
                if top_action is not None and (action_is_stale or action_is_empty):
                    original = data
                    data = dict(top_action)
                    mechanical_feedback.append(protocol_state(
                        "LLMAdapterState",
                        "route_repaired",
                        "llm_adapter",
                        repairs=[ProtocolIssue(
                            "false_route_policy",
                            "Replaced mismatched false_model_search route with the top false continuation card.",
                        ).to_dict()],
                        normalized_action=compact_tool_signature(data),
                        original_action=compact_tool_signature(original),
                    ))
            sig = compact_tool_signature(data)
            if sig in failed_signatures:
                mechanical_feedback.append(protocol_state(
                    "MechanicalResponse",
                    "duplicate_failed_call",
                    "scheduler",
                    tool="false_model_search",
                    need_hint="Do not repeat this exact failed false_model_search call; change routes/sizes/seeds or switch to midpoint/lemma_chain.",
                ))
                continue
            found, false_state = false_model_search_detailed(
                h_eq,
                g_eq,
                data,
                8,
                semantic_context=semantic_context,
            )
            if found and try_false_artifact_attributed(
                "llm:false_model_search",
                found,
                source="llm_tool_call",
                detail={"signature": sig},
            ):
                return "accepted_false_llm"
            if isinstance(false_state, dict):
                false_state = apply_false_route_memory(false_state, tried_false_routes, float(data.get("budget") or 8))
            failed_signatures.add(sig)
            mechanical_feedback.append(protocol_state(
                "MechanicalResponse",
                "stuck",
                "false_model_search",
                tool="false_model_search",
                tool_state=false_state,
                recommended_next_call=false_state.get("recommended_next_call") if isinstance(false_state, dict) else None,
                untried_requested_routes=false_state.get("untried_requested_routes") if isinstance(false_state, dict) else None,
                need_hint=false_state.get("need_hint") if isinstance(false_state, dict) else "Try a different false-search route, or switch to a true-side midpoint if the finite search is unproductive.",
            ))
            continue
        if (prefer_false is True or (prefer_false == "balanced" and false_cards_available)) and data.get("kind") == "tool_call":
            raw_tool = str(data.get("tool") or "").strip()
            tool = TOOL_ALIASES.get(raw_tool, raw_tool)
            if tool not in {"false_model_search", "false_model_family", "lemma_chain", "lemma_hint", "midpoint", "midpoint_chain"}:
                mechanical_feedback.append(protocol_state(
                    "MechanicalResponse",
                    "suppressed_in_false_preferred_pass",
                    "scheduler",
                    tool=tool,
                    need_hint="Return false_model_search/false_model_hint with concrete routes, or a real midpoint/lemma_chain. Do not repeat true-side tool calls in this pass.",
                ))
                failed_signatures.add(compact_tool_signature(data))
                continue
        body = None
        candidate_route = "llm:goal_proof"
        candidate_source = "llm_direct_artifact"
        if is_hint_payload(data):
            data = cap_hint_payload_budget(data, hint_budget_cap)
            sig = compact_tool_signature(data)
            if sig in failed_signatures:
                mechanical_feedback.append(protocol_state(
                    "MechanicalResponse",
                    "duplicate_failed_hint",
                    "scheduler",
                    need_hint="Do not repeat this exact failed midpoint/lemma payload; repair it using the frontier and closest_pairs.",
                ))
                continue
            hint_tool = capability_tool_for_action(data)
            gate_state = capability_gate_state(hint_tool, capability_mask)
            if gate_state is not None:
                mechanical_feedback.append(gate_state)
                failed_signatures.add(sig)
                continue
            body, state = hint_payload_attempt(data, h_eq, g_eq, capability_mask=capability_mask)
            candidate_route = "llm:hint_payload"
            candidate_source = "llm_hint"
            mechanical_feedback.append(state)
            if not body:
                failed_signatures.add(sig)
        elif data.get("kind") == "tool_call":
            sig = compact_tool_signature(data)
            if sig in failed_signatures:
                mechanical_feedback.append(protocol_state(
                    "MechanicalResponse",
                    "duplicate_failed_call",
                    "scheduler",
                    tool=data.get("tool"),
                    need_hint="Do not repeat this exact failed tool call; change arguments or switch strategy.",
                ))
                continue
            body, tool_state = run_tool_call_detailed(
                data,
                h_eq,
                g_eq,
                capability_mask=capability_mask,
                verify_candidates=True,
            )
            candidate_route = f"llm:tool:{data.get('tool')}"
            candidate_source = "llm_tool_call"
            if body and isinstance(tool_state, dict) and tool_state.get("already_judged_accepted"):
                return "accepted_true_llm"
            if not body:
                failed_signatures.add(sig)
                mechanical_feedback.append(protocol_state(
                    "MechanicalResponse",
                    "stuck",
                    str(data.get("tool") or "tool_call"),
                    tool=data.get("tool"),
                    tool_state=tool_state,
                    need_hint="This tool did not produce a proof body for the current H/G; use SearchState closest_pairs to propose a midpoint or choose another bounded tool.",
                ))
        if not body:
            body = data.get("proof") or data.get("body")
        if isinstance(body, str) and body.strip():
            result = judge_true_attributed(candidate_route, body, source=candidate_source)
            if result.get("status") == "accepted":
                return "accepted_true_llm"
            mechanical_feedback.append(protocol_state(
                "MechanicalResponse",
                "judge_rejected_true_body",
                "lean_judge",
                errors=[ProtocolIssue("judge_rejected", short_text(result.get("stderr") or result.get("message") or "", 800)).to_dict()],
                judge_status=result.get("status"),
                need_hint="Repair the proof body or propose a smaller midpoint/lemma chain that the mechanical prover can stitch.",
            ))
    if feedback_sink is not None:
        feedback_sink.clear()
        feedback_sink.extend(mechanical_feedback[-10:])
    return None


def solve(problem: dict[str, Any], budget: float) -> str:
    solve_started = time.monotonic()
    try:
        h_eq = parse_equation(problem["equation1"])
        g_eq = parse_equation(problem["equation2"])
    except Exception:
        return "parse_failed"
    semantic_context = implication_semantics(problem)
    semantic_state = semantic_status_state(semantic_context)
    false_failure_feedback: list[dict[str, Any]] = []
    early_true_feedback: list[dict[str, Any]] = []

    # The executable judge can express an infinite Type-level model, and the
    # protocol has structured and whole-artifact adapters. An Austin implication is
    # not a reason to buy more finite-search time, but it is exactly the case
    # where System 2 may be able to propose a compact Type-level artifact.
    if semantic_context.get("current_solver_certificate_status") == "requires_infinite_model_artifact":
        verified_artifact = verified_symbolic_model_artifact(semantic_context)
        if verified_artifact:
            verified_result = judge_infinite_model_artifact_attributed(
                "memory:verified_symbolic_model",
                verified_artifact,
                detail={
                    "eq1_id": semantic_context.get("eq1_id"),
                    "eq2_id": semantic_context.get("eq2_id"),
                    "lesson_status": "mechanically_verified",
                },
            )
            if verified_result.get("status") == "accepted":
                return "accepted_false_verified_symbolic_memory"
        remaining = max(0.0, budget - (time.monotonic() - solve_started))
        if remaining >= 8.0:
            status = try_llm_collaboration(
                h_eq,
                g_eq,
                remaining,
                max_rounds=3,
                collaboration_goal=(
                    "Audited semantics say finite countermodels are impossible "
                    "but the unrestricted implication is false. Do not search "
                    "finite tables. Prefer a structured symbolic_model_plan over "
                    "an infinite carrier; if Lean rejects one component, return a "
                    "symbolic_model_patch for only that failed component. A complete "
                    "compact infinite_model artifact remains an expert fast path."
                ),
                initial_feedback=[semantic_state],
                prefer_false=True,
                semantic_context=semantic_context,
                allow_infinite_model_artifacts=True,
            )
            if status:
                return status
        print(json.dumps(semantic_state, ensure_ascii=False), file=sys.stderr)
        return "semantic_solver_capability_gap"

    # Cheap false witnesses first.
    found = None
    if finite_countermodel_search_allowed(semantic_context):
        found = small_false_search(h_eq, g_eq, budget=min(4.0, max(1.0, budget * 0.08)))
    if found and try_false_attributed("native:false:small_false_search", *found, source="native_false_search"):
        return "accepted_false"

    # Goal-directed propagation catches sparse countermodels by searching
    # around a concrete Skolem point where the goal must fail.
    found, false_state = false_model_search_detailed(
        h_eq,
        g_eq,
        {"routes": ["model_finder_v2:n=4", "model_finder_v2:n=5"], "budget": min(8.0, max(2.0, budget * 0.08))},
        6,
        semantic_context=semantic_context,
    )
    if found and try_false_artifact_attributed("native:false:model_finder_v2_early", found, source="native_false_search"):
        return "accepted_false_v2"
    if not found and isinstance(false_state, dict):
        false_failure_feedback.append(false_state)

    # Compact extensions are cheap enough to scout before the broad true
    # battery, and occupy a different search language from arbitrary tables.
    # Keeping this as an ordinary false_model_search route makes the exact
    # state available to the LLM and lets later calls vary the factorization.
    remaining = max(0.0, budget - (time.monotonic() - solve_started))
    if remaining >= 6.0:
        found, skew_state = false_model_search_detailed(
            h_eq,
            g_eq,
            {
                "routes": ["skew_product:2x3"],
                "budget": min(4.0, remaining),
            },
            4,
            semantic_context=semantic_context,
        )
        if found and try_false_artifact_attributed(
            "native:false:skew_product_early",
            found,
            source="native_false_search",
            detail={"factorization": "2x3"},
        ):
            return "accepted_false_skew_product"
        if not found and isinstance(skew_state, dict):
            false_failure_feedback.append(skew_state)

    # One-sided variables in H are a strong, cheap signal for collapse,
    # projection, or row-constancy.  Give those helpers a short native scout
    # before speculative graph bodies or LLM routing.  A miss still falls
    # through to the larger late portfolio.
    if standard_aux_plausible_h(h_eq):
        early_aux_lemmas = implied_standard_aux_lemmas(h_eq)
        early_aux_budget = min(4.0, max(1.0, budget * 0.02))
        if early_aux_lemmas:
            early_aux_budget = min(
                8.0,
                max(
                    5.0 if any(kind in early_aux_lemmas for kind in ("proj_l", "proj_r")) else 4.0,
                    budget * 0.025,
                ),
            )
        aux_body, aux_state = standard_aux_superposition_attempt(
            h_eq,
            g_eq,
            {
                "lemmas": early_aux_lemmas or ["const", "proj_l", "proj_r", "rowconst"],
                "budget": early_aux_budget,
            },
        )
        if aux_body:
            result = judge_true_attributed(
                "native:true:standard_aux_superposition_early",
                aux_body,
                source="native_early_true_tool",
                detail={
                    "family": "standard_aux_superposition",
                    "used_aux": aux_state.get("used_aux") if isinstance(aux_state, dict) else None,
                },
            )
            if result.get("status") == "accepted":
                return "accepted_true_standard_aux_superposition"

    if broad_grounding_orientable(h_eq["lhs"], h_eq["rhs"]):
        bg_body, bg_state = broad_grounding_derived_body(
            h_eq,
            g_eq,
            budget=min(4.0, max(1.0, budget * 0.04)),
        )
        if bg_body:
            result = judge_true_attributed(
                "native:true:broad_grounding_derived_early",
                bg_body,
                source="native_early_true_tool",
                detail={
                    "family": "broad_grounding_derived",
                    "derived_helper": bg_state.get("derived_helper") if isinstance(bg_state, dict) else None,
                },
            )
            if result.get("status") == "accepted":
                return "accepted_true_broad_grounding_derived"

    if repeated_self_absorption_h(h_eq, g_eq):
        remaining = max(0.0, budget - (time.monotonic() - solve_started))
        if remaining >= 10.0:
            nested_tail_shape = nested_tail_absorption_h(h_eq, g_eq)
            chain_budget = (
                min(40.0, remaining, max(36.0, remaining * 0.04))
                if nested_tail_shape
                else min(14.0, remaining, max(12.0, remaining * 0.02))
            )
            chain_names = (
                ["nested_tail_absorption"]
                if nested_tail_shape
                else ["generic_right_square_absorption"]
            )
            chain_body, chain_state = helper_chain_portfolio_attempt(
                h_eq,
                g_eq,
                {"chains": chain_names, "budget": chain_budget},
                budget=chain_budget,
            )
            if chain_body:
                result = judge_true_attributed(
                    "native:true:helper_chain_portfolio_early",
                    chain_body,
                    source="native_early_true_tool",
                    detail={
                        "family": "helper_chain_portfolio",
                        "winning_chain": chain_state.get("winning_chain") if isinstance(chain_state, dict) else None,
                        "proved_lemmas": chain_state.get("proved_lemmas") if isinstance(chain_state, dict) else None,
                    },
                )
                if result.get("status") == "accepted":
                    return "accepted_true_helper_chain_portfolio"
            elif isinstance(chain_state, dict):
                early_true_feedback.append(chain_state)

    # Focused trusted true tools.
    for route, body in proof_candidates_with_sources(h_eq, g_eq):
        if try_true_attributed(f"native:true:{route}", body, source="native_true_tool"):
            return "accepted_true"

    initial_feedback = [{
        "kind": "initial_direct_graph_state",
        "status": "direct_mechanical_routes_available_for_feedback",
        "search_state": graph_search_state(h_eq, g_eq, status="direct_goal_not_connected"),
        "need_hint": "Use frontier/closest_pairs to propose a bridge midpoint, or choose the top ranked trusted tool.",
    }, *early_true_feedback[-2:]]

    if repeated_self_absorption_h(h_eq, g_eq):
        remaining = max(0.0, budget - (time.monotonic() - solve_started))
        if remaining >= 8.0:
            early_llm_budget = min(30.0, remaining)
            hint_budget_cap = min(12.0, max(6.0, remaining * 0.08))
            status = try_llm_collaboration(
                h_eq,
                g_eq,
                early_llm_budget,
                max_rounds=2,
                collaboration_goal=(
                    "Early true-side pass for repeated self-absorption. "
                    "Native direct proof and bounded forward saturation did not close. "
                    "Propose a concrete midpoint or short lemma_chain of absorption/"
                    "contraction bridges; do not return placeholder equations or the "
                    "target goal itself as a midpoint. Any midpoint-chain mechanical "
                    f"budget is capped at about {hint_budget_cap:.1f}s in this pass."
                ),
                initial_feedback=initial_feedback,
                semantic_context=semantic_context,
                hint_budget_cap=hint_budget_cap,
            )
            if status:
                return status

    # Stronger bounded false search. Give the goal-directed v2 finder a
    # dedicated slice before mixing it with stochastic routes; it can need a
    # few seconds to reach the Skolem branch that violates the goal.
    found, false_state = false_model_search_detailed(
        h_eq,
        g_eq,
        {
            "routes": ["model_finder_v2:n=6", "model_finder_v2:n=7", "model_finder_v2:n=8"],
            "budget": min(90.0, max(45.0, budget * 0.08)),
        },
        8,
        semantic_context=semantic_context,
    )
    if found and try_false_artifact_attributed("native:false:model_finder_v2_late", found, source="native_false_search"):
        return "accepted_false_v2"
    if not found and isinstance(false_state, dict):
        false_failure_feedback.append(false_state)

    exact_action = promoted_exact_false_action(false_failure_feedback)
    if exact_action is not None:
        found, exact_state = false_model_search_detailed(
            h_eq,
            g_eq,
            exact_action,
            1,
            semantic_context=semantic_context,
        )
        if found and try_false_artifact_attributed("native:false:exact_continuation", found, source="native_false_search"):
            return "accepted_false_exact_continuation"
        if not found and isinstance(exact_state, dict):
            false_failure_feedback.append(exact_state)

    if should_try_collaboration_first(h_eq, g_eq) and not false_strategy_cards(false_failure_feedback):
        status = try_llm_collaboration(
            h_eq,
            g_eq,
            budget,
            max_rounds=2,
            collaboration_goal=(
                "Collaboration pass after focused native tools: choose the top "
                "ranked trusted tool or propose an equivalent lemma_chain/midpoint. "
                "The mechanical side will verify everything and fall back if this fails."
            ),
            initial_feedback=initial_feedback,
            semantic_context=semantic_context,
        )
        if status:
            return status

    # False-side collaboration checkpoint. This gives System 2 one chance to
    # choose the next route from concrete false-search telemetry before the
    # native portfolio tries that route silently. It is intentionally gated on
    # strategy cards so true-side problems do not pay for a blind false prompt.
    if false_strategy_cards(false_failure_feedback):
        remaining = max(0.0, budget - (time.monotonic() - solve_started))
        status = try_llm_collaboration(
            h_eq,
            g_eq,
            remaining,
            max_rounds=1,
            collaboration_goal=(
                "False-route collaboration pass after focused true tools and "
                "goal-directed false search failed. Follow the concrete "
                "false_model_search continuation from the telemetry unless you "
                "can provide a verified table or a genuinely better route."
            ),
            initial_feedback=[{
                "kind": "false_route_collaboration_state",
                "status": "native_v2_false_search_failed",
                "native_false_failed_attempts": false_failure_feedback[-3:],
                "need_hint": "Select one untried false_model_search continuation from the telemetry; do not repeat tried routes.",
            }],
            prefer_false=True,
            semantic_context=semantic_context,
        )
        if status:
            return status

    # Fall back to the cheap stochastic witness route and structured
    # polynomial search. These use the same certificate renderer, so any found
    # table is still judge-verified before returning.
    late_false_budget = min(90.0, max(45.0, budget * 0.08))
    if sympy_sat_available():
        # The exact SAT route needs a wide window to be useful. Grant it
        # explicitly here (previously a hidden 120s floor inside
        # false_model_search_detailed), but never beyond half the remaining
        # global budget — the solve() contract outranks any single route.
        remaining_now = max(0.0, budget - (time.monotonic() - solve_started))
        late_false_budget = min(max(late_false_budget, 120.0), max(5.0, remaining_now * 0.5))
    found, false_state = false_model_search_detailed(
        h_eq,
        g_eq,
        {
            "routes": [
                "local_search:n=6:seed=2",
                "model_finder_v2:n=7",
                "model_finder_v2:n=8",
                "sympy_sat:n=6",
                "cp_sat:n=6",
                "poly_ce:tier=2:nmax=13",
                "structured_ce:max_n=7",
            ],
            "budget": late_false_budget,
        },
        8,
        semantic_context=semantic_context,
    )
    if found and try_false_artifact_attributed("native:false:portfolio_late", found, source="native_false_search"):
        return "accepted_false"
    if not found and isinstance(false_state, dict):
        false_failure_feedback.append(false_state)

    # Late source-independent true portfolio.  These are the minimal native
    # counterparts of every mechanism class that used to be supplied by the
    # compatibility solver: grounding/collapse, auxiliary superposition,
    # saturation, and broad goal superposition.
    remaining = max(0.0, budget - (time.monotonic() - solve_started))
    deep_budget = min(120.0, max(12.0, remaining * 0.15))
    deep_failure_feedback: list[dict[str, Any]] = []
    for route, body, state in native_deep_true_candidates(h_eq, g_eq, deep_budget):
        result = judge_true_attributed(
            f"native:true:{route}",
            body,
            source="native_deep_true_tool",
            detail={"family": state.get("family") if isinstance(state, dict) else None},
        )
        if result.get("status") == "accepted":
            return f"accepted_true_{route.split(':', 1)[0]}"
        deep_failure_feedback.append(protocol_state(
            "MechanicalResponse",
            "judge_rejected_true_body",
            route,
            tool_state=state,
            judge_status=result.get("status"),
            need_hint="This native certificate was rejected; use its family as evidence and propose a different midpoint or route.",
        ))
    deep_failure_feedback = deep_failure_feedback[-6:]

    # Give System 2 a load-bearing late chance. This is where LLM-proposed
    # midpoints/search routes can complement the bounded native portfolio while
    # remaining checked by the same mechanical consumers and Lean judge.
    remaining = max(0.0, budget - (time.monotonic() - solve_started))
    late_llm_feedback: list[dict[str, Any]] = []
    status = try_llm_collaboration(
        h_eq,
        g_eq,
        remaining,
        max_rounds=2,
        collaboration_goal=(
            "Late collaboration pass after native deterministic tools failed. "
            "Prefer a real bridge midpoint/lemma_chain or a concrete false_model_hint. "
            "A useful midpoint will be proved as H=>M and then consumed as H+M=>G."
        ),
        initial_feedback=[{
            "kind": "late_system2_state",
            "status": "native_deep_tools_failed",
            "search_state": graph_search_state(h_eq, g_eq, status="native_deep_goal_not_connected"),
            "native_false_failed_attempts": false_failure_feedback[-3:],
            "native_deep_failed_attempts": deep_failure_feedback,
            "need_hint": "Propose a small midpoint with seed_h_args, or a concrete false_model_hint route not already covered by default search.",
        }],
        prefer_false="balanced",
        feedback_sink=late_llm_feedback,
        semantic_context=semantic_context,
    )
    if status:
        return status

    # LLM fallback: tool selection, helper chains, direct proof, or table.
    status = try_llm_collaboration(
        h_eq,
        g_eq,
        budget,
        max_rounds=3,
        collaboration_goal=(
            "Fallback collaboration pass after deterministic routes failed. "
            "Use mechanical feedback to avoid repeats and propose a bridge "
            "midpoint, lemma_chain, seed_terms, or a concrete false-model route."
        ),
        initial_feedback=[{
            "kind": "initial_direct_graph_state",
            "status": "direct_mechanical_routes_exhausted",
            "search_state": graph_search_state(h_eq, g_eq, status="direct_goal_not_connected"),
            "need_hint": "Use the frontier/closest_pairs to propose a bridge midpoint, or choose a different bounded tool route.",
        }, *false_failure_feedback[-3:], *deep_failure_feedback[-4:], *late_llm_feedback[-6:]],
        prefer_false=True,
        semantic_context=semantic_context,
    )
    return status or "unsolved"


def main() -> None:
    startup = read_msg()
    problem = startup.get("problem", startup)
    budget = float(startup.get("budget", {}).get("timeout_seconds", 3600))
    status = solve(problem, budget)
    print(f"[baby_solver] {problem.get('id')}: {status}", file=sys.stderr)


if __name__ == "__main__":
    main()
