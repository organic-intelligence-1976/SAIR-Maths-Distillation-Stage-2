"""Compatibility facade for the packed symbolic Type-model contract.

The competition solver must be self-contained, so the canonical implementation
lives in ``baby_solver.py``. Research orchestration imports these names through
this module to keep one action language and one repair behavior.
"""

from __future__ import annotations

from typing import Any

import baby_solver


INFINITE_MODEL_PLAN_VERSION = baby_solver.SYMBOLIC_MODEL_PLAN_VERSION
PLAN_KINDS = baby_solver.SYMBOLIC_MODEL_PLAN_KINDS
PATCH_KINDS = baby_solver.SYMBOLIC_MODEL_PATCH_KINDS
PART_FIELDS = baby_solver.SYMBOLIC_MODEL_PART_FIELDS


def is_infinite_model_plan(action: Any) -> bool:
    return baby_solver.is_symbolic_model_plan_payload(action)


def is_infinite_model_patch(action: Any) -> bool:
    return baby_solver.is_symbolic_model_patch_payload(action)


def normalize_infinite_model_plan(
    action: dict[str, Any],
) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    return baby_solver.normalize_symbolic_model_plan(action)


def merge_infinite_model_patch(
    base: dict[str, Any],
    patch: dict[str, Any],
) -> dict[str, Any]:
    return baby_solver.merge_symbolic_model_patch(base, patch)


def assemble_infinite_model_plan(
    action: dict[str, Any],
) -> tuple[str | None, dict[str, Any]]:
    return baby_solver.assemble_symbolic_model_plan(action)
