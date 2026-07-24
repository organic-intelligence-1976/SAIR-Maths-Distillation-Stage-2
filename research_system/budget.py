"""Stable research-layer access to renewable midpoint budget policies."""

from __future__ import annotations

import json
import random
from pathlib import Path
from typing import Any

from baby_solver import MidpointBudgetPolicy, RenewableBudgetBroker


POLICY_SCHEMA_VERSION = "sair-midpoint-budget-v1"


def normalize_budget_policy(value: Any, *, candidate_count: int = 5) -> dict[str, Any]:
    """Return the bounded canonical policy mapping used by the packed worker."""
    raw = value.get("budget_policy") if isinstance(value, dict) and isinstance(value.get("budget_policy"), dict) else value
    return MidpointBudgetPolicy.from_mapping(raw, candidate_count=candidate_count).to_mapping()


def load_budget_policy(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"budget policy must be a JSON object: {path}")
    return normalize_budget_policy(payload)


def budget_policy_record(value: Any) -> dict[str, Any]:
    policy = MidpointBudgetPolicy.from_mapping(normalize_budget_policy(value), candidate_count=5)
    return {
        "schema_version": POLICY_SCHEMA_VERSION,
        "policy_id": policy.policy_id,
        "budget_policy": policy.to_mapping(),
    }


def mutate_budget_policy(
    parent: Any,
    *,
    seed: int,
    sigma: float = 0.25,
) -> dict[str, Any]:
    """Create a reproducible bounded offspring policy for tournament search."""
    rng = random.Random(seed)
    raw = normalize_budget_policy(parent)
    scale_names = {
        "total_budget",
        "initial_grant",
        "grant_growth",
        "max_grant",
        "attain_priority",
        "consume_priority",
        "goal_priority",
        "relevance_weight",
        "reuse_weight",
        "exploration_weight",
        "progress_weight",
        "companion_success_weight",
        "failure_penalty",
        "tie_break_weight",
    }
    child = dict(raw)
    for name in scale_names:
        child[name] = float(raw[name]) * (2.0 ** rng.gauss(0.0, max(0.0, sigma)))
    child["max_grants_per_task"] = int(raw["max_grants_per_task"]) + rng.choice((-1, 0, 1))
    child["seed"] = rng.randrange(0, 2**31)
    return budget_policy_record(child)


__all__ = [
    "POLICY_SCHEMA_VERSION",
    "MidpointBudgetPolicy",
    "RenewableBudgetBroker",
    "budget_policy_record",
    "load_budget_policy",
    "mutate_budget_policy",
    "normalize_budget_policy",
]
