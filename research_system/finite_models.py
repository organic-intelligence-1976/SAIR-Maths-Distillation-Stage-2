"""Compact finite-model constructors with mechanically synthesized parameters."""

from __future__ import annotations

import math
import time
from collections import Counter
from dataclasses import asdict, dataclass
from itertools import product
from typing import Any

import baby_solver


SKEW_PRODUCT_VERSION = "sair-skew-product-v1"
SKEW_PRODUCT_KINDS = {
    "skew_model_search",
    "skew_product_search",
    "block_model_search",
}
BUNDLE_MODEL_VERSION = "sair-bundle-model-v1"
BUNDLE_MODEL_KINDS = {
    "bundle_model_search",
    "fiber_bundle_search",
    "patched_bundle_search",
}


def is_skew_product_action(action: Any) -> bool:
    if not isinstance(action, dict):
        return False
    kind = str(action.get("kind") or "").strip().lower()
    tool = str(action.get("tool") or "").strip().lower()
    return kind in SKEW_PRODUCT_KINDS or (
        kind == "tool_call" and tool in SKEW_PRODUCT_KINDS
    )


def is_bundle_model_action(action: Any) -> bool:
    if not isinstance(action, dict):
        return False
    kind = str(action.get("kind") or "").strip().lower()
    tool = str(action.get("tool") or "").strip().lower()
    return kind in BUNDLE_MODEL_KINDS or (
        kind == "tool_call" and tool in BUNDLE_MODEL_KINDS
    )


def _coerce_bool(value: Any, default: bool) -> bool:
    if value is None:
        return default
    if isinstance(value, str):
        lowered = value.strip().lower()
        if lowered in {"false", "0", "no", "off"}:
            return False
        if lowered in {"true", "1", "yes", "on"}:
            return True
    return bool(value)


@dataclass(frozen=True)
class SkewProductConfig:
    control_size: int = 2
    fiber_size: int = 3
    fiber_library: str = "affine"
    require_quotient_goal: bool = True
    time_budget: float = 15.0
    max_iterations: int = 96
    violation_batch: int = 12
    workers: int = 8
    seed: int = 0

    def normalized(self) -> "SkewProductConfig":
        control = max(1, min(6, int(self.control_size)))
        fiber = max(2, min(8, int(self.fiber_size)))
        if control * fiber > 40:
            control = max(1, 40 // fiber)
        library = str(self.fiber_library or "affine").strip().lower()
        if library not in {"affine", "affine_order"}:
            library = "affine"
        return SkewProductConfig(
            control_size=control,
            fiber_size=fiber,
            fiber_library=library,
            require_quotient_goal=_coerce_bool(self.require_quotient_goal, True),
            time_budget=max(0.5, min(300.0, float(self.time_budget))),
            max_iterations=max(1, min(500, int(self.max_iterations))),
            violation_batch=max(1, min(64, int(self.violation_batch))),
            workers=max(1, min(16, int(self.workers))),
            seed=int(self.seed),
        )


def config_from_action(action: dict[str, Any]) -> SkewProductConfig:
    source = action.get("skew_product")
    if not isinstance(source, dict):
        source = action
    return SkewProductConfig(
        control_size=int(source.get("control_size") or source.get("quotient_size") or 2),
        fiber_size=int(source.get("fiber_size") or 3),
        fiber_library=str(source.get("fiber_library") or "affine"),
        require_quotient_goal=_coerce_bool(
            source.get("require_quotient_goal"),
            True,
        ),
        time_budget=float(source.get("budget") or source.get("time_budget") or 15.0),
        max_iterations=int(source.get("max_iterations") or 96),
        violation_batch=int(source.get("violation_batch") or 12),
        workers=int(source.get("workers") or 8),
        seed=int(source.get("seed") or 0),
    ).normalized()


def normalize_skew_product_action(action: dict[str, Any]) -> dict[str, Any]:
    source = action.get("skew_product")
    if not isinstance(source, dict):
        source = action
    return {
        "kind": "skew_model_search",
        **asdict(config_from_action(source)),
    }


@dataclass(frozen=True)
class BundleModelConfig:
    fiber_sizes: tuple[int, ...] = (4, 2)
    fiber_library: str = "affine_patches"
    max_patches: int = 7
    quotient_table: tuple[tuple[int, ...], ...] | None = None
    require_quotient_goal: bool = True
    max_quotient_tables: int = 64
    time_budget: float = 30.0
    max_iterations: int = 128
    violation_batch: int = 12
    workers: int = 8
    seed: int = 0

    def normalized(self) -> "BundleModelConfig":
        fibers = tuple(max(1, min(12, int(value))) for value in self.fiber_sizes)
        if not 2 <= len(fibers) <= 6:
            raise ValueError("fiber_sizes must contain between two and six blocks")
        if sum(fibers) > 40:
            raise ValueError("bundle carrier is limited to 40 elements")
        library = str(self.fiber_library or "affine_patches").strip().lower()
        if library not in {"affine_patches"}:
            library = "affine_patches"
        quotient = self.quotient_table
        if quotient is not None:
            quotient = tuple(tuple(int(value) for value in row) for row in quotient)
            size = len(fibers)
            if len(quotient) != size or any(len(row) != size for row in quotient):
                raise ValueError("quotient_table dimensions must match fiber_sizes")
            if any(value < 0 or value >= size for row in quotient for value in row):
                raise ValueError("quotient_table contains an out-of-range element")
        elif len(fibers) > 3:
            raise ValueError(
                "an explicit quotient_table is required for more than three blocks"
            )
        carrier_size = sum(fibers)
        return BundleModelConfig(
            fiber_sizes=fibers,
            fiber_library=library,
            max_patches=max(0, min(carrier_size * carrier_size, int(self.max_patches))),
            quotient_table=quotient,
            require_quotient_goal=_coerce_bool(self.require_quotient_goal, True),
            max_quotient_tables=max(1, min(256, int(self.max_quotient_tables))),
            time_budget=max(0.5, min(300.0, float(self.time_budget))),
            max_iterations=max(1, min(500, int(self.max_iterations))),
            violation_batch=max(1, min(64, int(self.violation_batch))),
            workers=max(1, min(16, int(self.workers))),
            seed=int(self.seed),
        )


def bundle_config_from_action(action: dict[str, Any]) -> BundleModelConfig:
    source = action.get("bundle_model")
    if not isinstance(source, dict):
        source = action
    raw_fibers = source.get("fiber_sizes") or source.get("block_sizes") or [4, 2]
    if not isinstance(raw_fibers, (list, tuple)):
        raise ValueError("fiber_sizes must be a JSON array")
    raw_quotient = source.get("quotient_table")
    quotient = None
    if raw_quotient is not None:
        if not isinstance(raw_quotient, (list, tuple)):
            raise ValueError("quotient_table must be a square JSON array")
        quotient = tuple(tuple(int(value) for value in row) for row in raw_quotient)
    return BundleModelConfig(
        fiber_sizes=tuple(int(value) for value in raw_fibers),
        fiber_library=str(source.get("fiber_library") or "affine_patches"),
        max_patches=int(
            source["max_patches"]
            if source.get("max_patches") is not None
            else 7
        ),
        quotient_table=quotient,
        require_quotient_goal=_coerce_bool(
            source.get("require_quotient_goal"),
            True,
        ),
        max_quotient_tables=int(source.get("max_quotient_tables") or 64),
        time_budget=float(source.get("budget") or source.get("time_budget") or 30.0),
        max_iterations=int(source.get("max_iterations") or 128),
        violation_batch=int(source.get("violation_batch") or 12),
        workers=int(source.get("workers") or 8),
        seed=int(source.get("seed") or 0),
    ).normalized()


def normalize_bundle_model_action(action: dict[str, Any]) -> dict[str, Any]:
    source = action.get("bundle_model")
    if not isinstance(source, dict):
        source = action
    return {
        "kind": "bundle_model_search",
        **asdict(bundle_config_from_action(source)),
    }


def affine_fiber_library(size: int, *, include_order: bool = False) -> list[dict[str, Any]]:
    """Return a finite menu of total binary maps on one fiber."""
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
        rows.append({
            "kind": "affine",
            "params": [a, b, c],
            "table": table,
        })
    if include_order:
        for kind, function in (
            ("min", min),
            ("max", max),
        ):
            table = tuple(
                function(left, right)
                for left in range(size)
                for right in range(size)
            )
            if table in seen:
                continue
            seen.add(table)
            rows.append({"kind": kind, "params": [], "table": table})
    return rows


def affine_rectangular_library(
    left_size: int,
    right_size: int,
    output_size: int,
) -> list[dict[str, Any]]:
    """Return affine maps between possibly different finite fibers."""
    rows: list[dict[str, Any]] = []
    seen: set[tuple[int, ...]] = set()
    for a, b, c in product(range(output_size), repeat=3):
        table = tuple(
            (a * left + b * right + c) % output_size
            for left in range(left_size)
            for right in range(right_size)
        )
        if table in seen:
            continue
        seen.add(table)
        rows.append({
            "kind": "affine",
            "params": [a, b, c],
            "table": table,
        })
    return rows


def _cp_eval(
    model: Any,
    term: Any,
    env: dict[str, Any],
    flat_operation: list[Any],
    carrier_size: int,
    counter: list[int],
    prefix: str,
) -> Any:
    if term[0] == "var":
        return env[term[1]]
    left = _cp_eval(
        model,
        term[1],
        env,
        flat_operation,
        carrier_size,
        counter,
        prefix,
    )
    right = _cp_eval(
        model,
        term[2],
        env,
        flat_operation,
        carrier_size,
        counter,
        prefix,
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


def _find_h_violations(
    equation: dict[str, Any],
    table: list[list[int]],
    *,
    limit: int,
    deadline: float,
) -> tuple[list[tuple[int, ...]], int, bool]:
    variables = equation["variables"]
    carrier_size = len(table)
    violations: list[tuple[int, ...]] = []
    checked = 0
    for values in product(range(carrier_size), repeat=len(variables)):
        if time.monotonic() >= deadline:
            return violations, checked, False
        env = dict(zip(variables, values))
        checked += 1
        if (
            baby_solver.eval_term(equation["lhs"], env, table)
            == baby_solver.eval_term(equation["rhs"], env, table)
        ):
            continue
        violations.append(tuple(int(value) for value in values))
        if len(violations) >= limit:
            return violations, checked, False
    return violations, checked, True


def _goal_witness(
    equation: dict[str, Any],
    table: list[list[int]],
    values: dict[str, int],
) -> dict[str, Any]:
    left = baby_solver.eval_term(equation["lhs"], values, table)
    right = baby_solver.eval_term(equation["rhs"], values, table)
    return {
        "env": dict(values),
        "lhs": left,
        "rhs": right,
        "separates": left != right,
    }


def _parameter_summary(
    solver: Any,
    control: dict[tuple[int, int], Any],
    selectors: dict[tuple[int, int], Any],
    library: list[dict[str, Any]],
    config: SkewProductConfig,
) -> dict[str, Any]:
    control_table = [
        [int(solver.Value(control[(left, right)])) for right in range(config.control_size)]
        for left in range(config.control_size)
    ]
    fiber_maps = []
    histogram: Counter[str] = Counter()
    for left in range(config.control_size):
        for right in range(config.control_size):
            index = int(solver.Value(selectors[(left, right)]))
            row = library[index]
            label = (
                f"affine:{','.join(str(value) for value in row['params'])}"
                if row["kind"] == "affine"
                else str(row["kind"])
            )
            histogram[label] += 1
            fiber_maps.append({
                "control_cell": [left, right],
                "selector": index,
                "kind": row["kind"],
                "params": list(row["params"]),
            })
    parameter_count = config.control_size * config.control_size * 2
    explicit_cells = (
        config.control_size * config.fiber_size
    ) ** 2
    selector_bits = math.ceil(math.log2(max(1, len(library))))
    approximate_bits = config.control_size * config.control_size * (
        math.ceil(math.log2(max(2, config.control_size))) + selector_bits
    )
    return {
        "control_table": control_table,
        "fiber_maps": fiber_maps,
        "fiber_map_histogram": dict(histogram),
        "parameter_count": parameter_count,
        "explicit_table_cells": explicit_cells,
        "cell_to_parameter_ratio": round(explicit_cells / max(1, parameter_count), 3),
        "approximate_description_bits": approximate_bits,
    }


def _skew_to_bundle_suggestion(config: SkewProductConfig) -> dict[str, Any]:
    fibers = [config.fiber_size for _ in range(config.control_size)]
    fibers[0] += 1
    carrier_size = sum(fibers)
    return {
        "kind": "bundle_model_search",
        "fiber_sizes": fibers,
        "fiber_library": "affine_patches",
        "max_patches": max(2, math.ceil(carrier_size * carrier_size * 0.15)),
        "require_quotient_goal": config.require_quotient_goal,
        "budget": round(min(300.0, max(15.0, config.time_budget * 1.5)), 1),
        "why": (
            "relax the failed equal-fiber extension to a non-uniform quotient "
            "bundle with sparse local exceptions"
        ),
    }


def _bundle_continuation_suggestions(
    config: BundleModelConfig,
) -> list[dict[str, Any]]:
    carrier_size = sum(config.fiber_sizes)
    patch_step = max(1, math.ceil(carrier_size * carrier_size * 0.05))
    patch_suggestion = {
        "kind": "bundle_model_search",
        "fiber_sizes": list(config.fiber_sizes),
        "fiber_library": "affine_patches",
        "max_patches": min(
            carrier_size * carrier_size,
            config.max_patches + patch_step,
        ),
        "require_quotient_goal": config.require_quotient_goal,
        "budget": round(min(300.0, max(15.0, config.time_budget * 1.25)), 1),
        "why": "retain the quotient shape and relax only the sparse exception budget",
    }
    suggestions = [patch_suggestion]
    grown = list(config.fiber_sizes)
    grown[grown.index(max(grown))] += 1
    if sum(grown) <= 40:
        grown_size = sum(grown)
        grow_suggestion = {
            "kind": "bundle_model_search",
            "fiber_sizes": grown,
            "fiber_library": "affine_patches",
            "max_patches": max(
                config.max_patches,
                math.ceil(grown_size * grown_size * 0.15),
            ),
            "require_quotient_goal": config.require_quotient_goal,
            "budget": round(min(300.0, max(15.0, config.time_budget * 1.5)), 1),
            "why": "increase the carrier by one while preserving the quotient-bundle language",
        }
        if config.max_patches / max(1, carrier_size * carrier_size) >= 0.15:
            suggestions.insert(0, grow_suggestion)
        else:
            suggestions.append(grow_suggestion)
    return suggestions


def _equation_holds(
    equation: dict[str, Any],
    table: list[list[int]],
) -> bool:
    variables = equation["variables"]
    return all(
        baby_solver.eval_term(
            equation["lhs"],
            dict(zip(variables, values)),
            table,
        )
        == baby_solver.eval_term(
            equation["rhs"],
            dict(zip(variables, values)),
            table,
        )
        for values in product(range(len(table)), repeat=len(variables))
    )


def _bundle_quotient_candidates(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    config: BundleModelConfig,
    deadline: float,
) -> tuple[list[list[list[int]]], int, bool]:
    if config.quotient_table is not None:
        table = [list(row) for row in config.quotient_table]
        valid = _equation_holds(h_eq, table) and (
            not config.require_quotient_goal or _equation_holds(g_eq, table)
        )
        return ([table] if valid else []), 1, True

    size = len(config.fiber_sizes)
    candidates: list[list[list[int]]] = []
    examined = 0
    for flat in product(range(size), repeat=size * size):
        if time.monotonic() >= deadline:
            return candidates, examined, False
        examined += 1
        table = [
            list(flat[row * size : (row + 1) * size])
            for row in range(size)
        ]
        if not _equation_holds(h_eq, table):
            continue
        if config.require_quotient_goal and not _equation_holds(g_eq, table):
            continue
        candidates.append(table)
        if len(candidates) >= config.max_quotient_tables:
            return candidates, examined, False
    return candidates, examined, True


def _bundle_parameter_summary(
    solver: Any,
    quotient_table: list[list[int]],
    config: BundleModelConfig,
    selectors: dict[tuple[int, int], Any],
    libraries: dict[tuple[int, int], list[dict[str, Any]]],
    patches: dict[tuple[int, int], Any],
    operation: dict[tuple[int, int], Any],
    base_values: dict[tuple[int, int], Any],
    element_coordinates: list[tuple[int, int]],
) -> dict[str, Any]:
    fiber_maps = []
    for left_block in range(len(config.fiber_sizes)):
        for right_block in range(len(config.fiber_sizes)):
            key = (left_block, right_block)
            index = int(solver.Value(selectors[key]))
            selected = libraries[key][index]
            fiber_maps.append({
                "quotient_cell": [left_block, right_block],
                "output_block": quotient_table[left_block][right_block],
                "selector": index,
                "kind": selected["kind"],
                "params": list(selected["params"]),
            })

    patch_rows = []
    for (left, right), patch in patches.items():
        if not solver.BooleanValue(patch):
            continue
        left_block, left_fiber = element_coordinates[left]
        right_block, right_fiber = element_coordinates[right]
        output = int(solver.Value(operation[(left, right)]))
        output_block, output_fiber = element_coordinates[output]
        patch_rows.append({
            "global_cell": [left, right],
            "quotient_cell": [left_block, right_block],
            "fiber_cell": [left_fiber, right_fiber],
            "base_fiber_value": int(solver.Value(base_values[(left, right)])),
            "output_block": output_block,
            "output_fiber_value": output_fiber,
        })

    quotient_size = len(config.fiber_sizes)
    symbolic_parameter_count = quotient_size * quotient_size * 2 + len(patch_rows) * 3
    explicit_cells = sum(config.fiber_sizes) ** 2
    return {
        "quotient_table": quotient_table,
        "fiber_sizes": list(config.fiber_sizes),
        "fiber_maps": fiber_maps,
        "patches": patch_rows,
        "patch_count": len(patch_rows),
        "max_patches": config.max_patches,
        "symbolic_parameter_count": symbolic_parameter_count,
        "explicit_table_cells": explicit_cells,
        "cell_to_parameter_ratio": round(
            explicit_cells / max(1, symbolic_parameter_count),
            3,
        ),
    }


def _bundle_candidate_search(
    cp_model: Any,
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    config: BundleModelConfig,
    quotient_table: list[list[int]],
    deadline: float,
    candidate_index: int,
) -> tuple[str, list[list[int]] | None, dict[str, Any]]:
    fiber_sizes = config.fiber_sizes
    quotient_size = len(fiber_sizes)
    carrier_size = sum(fiber_sizes)
    offsets: list[int] = []
    element_coordinates: list[tuple[int, int]] = []
    offset = 0
    for block, size in enumerate(fiber_sizes):
        offsets.append(offset)
        element_coordinates.extend((block, fiber) for fiber in range(size))
        offset += size

    model = cp_model.CpModel()
    libraries: dict[tuple[int, int], list[dict[str, Any]]] = {}
    selectors: dict[tuple[int, int], Any] = {}
    for left_block in range(quotient_size):
        for right_block in range(quotient_size):
            output_block = quotient_table[left_block][right_block]
            library = affine_rectangular_library(
                fiber_sizes[left_block],
                fiber_sizes[right_block],
                fiber_sizes[output_block],
            )
            key = (left_block, right_block)
            libraries[key] = library
            selectors[key] = model.NewIntVar(
                0,
                len(library) - 1,
                f"bundle_selector_{left_block}_{right_block}",
            )

    operation: dict[tuple[int, int], Any] = {}
    base_values: dict[tuple[int, int], Any] = {}
    patches: dict[tuple[int, int], Any] = {}
    for left in range(carrier_size):
        left_block, left_fiber = element_coordinates[left]
        for right in range(carrier_size):
            right_block, right_fiber = element_coordinates[right]
            key = (left_block, right_block)
            output_block = quotient_table[left_block][right_block]
            output_size = fiber_sizes[output_block]
            output_offset = offsets[output_block]
            base = model.NewIntVar(
                0,
                output_size - 1,
                f"bundle_base_{left}_{right}",
            )
            outputs = [
                int(row["table"][left_fiber * fiber_sizes[right_block] + right_fiber])
                for row in libraries[key]
            ]
            model.AddElement(selectors[key], outputs, base)
            value = model.NewIntVar(
                output_offset,
                output_offset + output_size - 1,
                f"bundle_operation_{left}_{right}",
            )
            patched = model.NewBoolVar(f"bundle_patch_{left}_{right}")
            model.Add(value == output_offset + base).OnlyEnforceIf(patched.Not())
            model.Add(value != output_offset + base).OnlyEnforceIf(patched)
            operation[(left, right)] = value
            base_values[(left, right)] = base
            patches[(left, right)] = patched
    model.Add(sum(patches.values()) <= config.max_patches)

    flat_operation = [
        operation[(left, right)]
        for left in range(carrier_size)
        for right in range(carrier_size)
    ]
    goal_aux = [0]
    goal_env = {
        variable: model.NewIntVar(
            0,
            carrier_size - 1,
            f"bundle_goal_witness_{variable}",
        )
        for variable in g_eq["variables"]
    }
    goal_left = _cp_eval(
        model,
        g_eq["lhs"],
        goal_env,
        flat_operation,
        carrier_size,
        goal_aux,
        "bundle_goal",
    )
    goal_right = _cp_eval(
        model,
        g_eq["rhs"],
        goal_env,
        flat_operation,
        carrier_size,
        goal_aux,
        "bundle_goal",
    )
    model.Add(goal_left != goal_right)

    h_constraints: set[tuple[int, ...]] = set()
    full_aux = [0]

    def add_h_assignment(values: tuple[int, ...]) -> None:
        if values in h_constraints:
            return
        h_constraints.add(values)
        env = dict(zip(h_eq["variables"], values))
        left = _cp_eval(
            model,
            h_eq["lhs"],
            env,
            flat_operation,
            carrier_size,
            full_aux,
            "bundle_h",
        )
        right = _cp_eval(
            model,
            h_eq["rhs"],
            env,
            flat_operation,
            carrier_size,
            full_aux,
            "bundle_h",
        )
        model.Add(left == right)

    for block_values in product(
        range(quotient_size),
        repeat=len(h_eq["variables"]),
    ):
        add_h_assignment(tuple(offsets[value] for value in block_values))
    for value in range(carrier_size):
        add_h_assignment(tuple(value for _ in h_eq["variables"]))

    events: list[dict[str, Any]] = []
    total_checked = 0
    last_summary: dict[str, Any] | None = None
    last_witness: dict[str, Any] | None = None
    for iteration in range(1, config.max_iterations + 1):
        remaining = deadline - time.monotonic()
        if remaining <= 0.05:
            break
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = max(0.05, remaining)
        solver.parameters.num_search_workers = config.workers
        solver.parameters.random_seed = config.seed + candidate_index + iteration - 1
        cp_status = solver.Solve(model)
        event: dict[str, Any] = {
            "iteration": iteration,
            "cp_status": solver.StatusName(cp_status),
            "wall_time": round(float(solver.WallTime()), 3),
            "branches": int(solver.NumBranches()),
            "conflicts": int(solver.NumConflicts()),
            "lifted_h_constraints": len(h_constraints),
        }
        if cp_status == cp_model.INFEASIBLE:
            events.append(event)
            return "infeasible", None, {
                "status": "quotient_candidate_infeasible",
                "quotient_table": quotient_table,
                "iterations": iteration,
                "events": events[-12:],
            }
        if cp_status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            event["reason"] = "solver_budget_or_unknown"
            events.append(event)
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
        witness = _goal_witness(g_eq, table, witness_env)
        last_witness = witness
        last_summary = _bundle_parameter_summary(
            solver,
            quotient_table,
            config,
            selectors,
            libraries,
            patches,
            operation,
            base_values,
            element_coordinates,
        )
        violations, checked, complete = _find_h_violations(
            h_eq,
            table,
            limit=config.violation_batch,
            deadline=deadline,
        )
        total_checked += checked
        event.update({
            "h_assignments_checked": checked,
            "h_scan_complete": complete,
            "h_violations_found": len(violations),
            "first_h_violation": (
                dict(zip(h_eq["variables"], violations[0]))
                if violations
                else None
            ),
            "goal_witness": witness,
            "patch_count": last_summary["patch_count"],
        })
        events.append(event)
        if complete and not violations:
            if not baby_solver.is_counterexample(h_eq, g_eq, table):
                return "internal_error", None, {
                    "status": "verification_mismatch",
                    "events": events[-12:],
                }
            return "found", table, {
                "status": "verified_countermodel",
                "quotient_table": quotient_table,
                "lifted_h_constraints": len(h_constraints),
                "iterations": iteration,
                "h_assignments_checked_total": total_checked,
                "goal_witness": witness,
                "parameters": last_summary,
                "events": events[-12:],
            }
        if not complete and not violations:
            break
        for values in violations:
            add_h_assignment(values)

    return "budget", None, {
        "status": "quotient_candidate_incomplete",
        "quotient_table": quotient_table,
        "lifted_h_constraints": len(h_constraints),
        "iterations": len(events),
        "h_assignments_checked_total": total_checked,
        "last_goal_witness": last_witness,
        "last_parameters": last_summary,
        "events": events[-12:],
    }


def bundle_counterexample_search(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    config: BundleModelConfig | None = None,
) -> tuple[str, list[list[int]] | None, dict[str, Any]]:
    """Synthesize a non-uniform quotient bundle with sparse local exceptions."""
    config = (config or BundleModelConfig()).normalized()
    try:
        from ortools.sat.python import cp_model
    except Exception:
        return "unavailable", None, {
            "kind": "BundleModelSearchState",
            "version": BUNDLE_MODEL_VERSION,
            "status": "unavailable",
            "reason": "ortools.sat.python.cp_model is not available",
            "config": asdict(config),
        }

    started = time.monotonic()
    deadline = started + config.time_budget
    candidates, quotient_tables_examined, enumeration_complete = (
        _bundle_quotient_candidates(h_eq, g_eq, config, deadline)
    )
    if not candidates:
        status = "family_infeasible" if enumeration_complete else "search_incomplete"
        return ("infeasible" if enumeration_complete else "budget"), None, {
            "kind": "BundleModelSearchState",
            "version": BUNDLE_MODEL_VERSION,
            "status": status,
            "config": asdict(config),
            "carrier_size": sum(config.fiber_sizes),
            "quotient_tables_examined": quotient_tables_examined,
            "quotient_candidates": 0,
            "seconds": round(time.monotonic() - started, 3),
            "suggested_next_actions": _bundle_continuation_suggestions(config),
            "need_hint": (
                "No quotient of the requested shape satisfies the required laws. "
                "Change fiber_sizes, provide a quotient_table, or relax "
                "require_quotient_goal."
            ),
        }

    candidate_events: list[dict[str, Any]] = []
    all_infeasible = enumeration_complete
    for candidate_index, quotient_table in enumerate(candidates):
        if time.monotonic() >= deadline:
            all_infeasible = False
            break
        status, table, state = _bundle_candidate_search(
            cp_model,
            h_eq,
            g_eq,
            config,
            quotient_table,
            deadline,
            candidate_index,
        )
        candidate_events.append({
            "candidate_index": candidate_index,
            "search_status": status,
            "quotient_table": quotient_table,
            "iterations": state.get("iterations"),
            "last_patch_count": (
                (state.get("parameters") or {}).get("patch_count")
                if isinstance(state.get("parameters"), dict)
                else (state.get("last_parameters") or {}).get("patch_count")
                if isinstance(state.get("last_parameters"), dict)
                else None
            ),
        })
        if table is not None:
            return "found", table, {
                "kind": "BundleModelSearchState",
                "version": BUNDLE_MODEL_VERSION,
                "status": "verified_countermodel",
                "config": asdict(config),
                "carrier_size": sum(config.fiber_sizes),
                "quotient_tables_examined": quotient_tables_examined,
                "quotient_candidates": len(candidates),
                "selected_quotient_index": candidate_index,
                "candidate_events": candidate_events[-12:],
                **state,
                "seconds": round(time.monotonic() - started, 3),
                "need_hint": None,
            }
        if status != "infeasible":
            all_infeasible = False

    if all_infeasible and len(candidate_events) == len(candidates):
        return "infeasible", None, {
            "kind": "BundleModelSearchState",
            "version": BUNDLE_MODEL_VERSION,
            "status": "family_infeasible",
            "config": asdict(config),
            "carrier_size": sum(config.fiber_sizes),
            "quotient_tables_examined": quotient_tables_examined,
            "quotient_candidates": len(candidates),
            "candidate_events": candidate_events[-12:],
            "seconds": round(time.monotonic() - started, 3),
            "suggested_next_actions": _bundle_continuation_suggestions(config),
            "need_hint": (
                "The quotient shapes are valid, but affine fiber maps with the "
                "current sparse-patch allowance are infeasible. Increase "
                "max_patches or change fiber_sizes."
            ),
        }
    return "budget", None, {
        "kind": "BundleModelSearchState",
        "version": BUNDLE_MODEL_VERSION,
        "status": "search_incomplete",
        "config": asdict(config),
        "carrier_size": sum(config.fiber_sizes),
        "quotient_tables_examined": quotient_tables_examined,
        "quotient_candidates": len(candidates),
        "candidate_events": candidate_events[-12:],
        "seconds": round(time.monotonic() - started, 3),
        "suggested_next_actions": _bundle_continuation_suggestions(config),
        "need_hint": (
            "The non-uniform bundle remains plausible but synthesis did not "
            "converge. Increase budget, supply a quotient_table, or adjust the "
            "fiber sizes and patch allowance."
        ),
    }


def analyze_congruence_decompositions(
    table: list[list[int]],
    *,
    max_partitions: int = 200_000,
    max_results: int = 32,
) -> dict[str, Any]:
    """Find small quotient/fiber decompositions of an explicit finite magma."""
    carrier_size = len(table)
    if carrier_size < 2 or any(len(row) != carrier_size for row in table):
        raise ValueError("operation table must be square and nonempty")
    if any(
        value < 0 or value >= carrier_size
        for row in table
        for value in row
    ):
        raise ValueError("operation table contains an out-of-range element")

    examined = 0
    truncated = False
    decompositions: list[dict[str, Any]] = []
    labels = [0] * carrier_size

    def inspect_partition(block_count: int) -> None:
        nonlocal examined
        examined += 1
        if block_count in {1, carrier_size}:
            return
        blocks = [
            [element for element, label in enumerate(labels) if label == block]
            for block in range(block_count)
        ]
        quotient = [[0 for _ in range(block_count)] for _ in range(block_count)]
        for left_block, left_elements in enumerate(blocks):
            for right_block, right_elements in enumerate(blocks):
                output_blocks = {
                    labels[table[left][right]]
                    for left in left_elements
                    for right in right_elements
                }
                if len(output_blocks) != 1:
                    return
                quotient[left_block][right_block] = next(iter(output_blocks))
        sizes = [len(block) for block in blocks]
        decompositions.append({
            "blocks": blocks,
            "block_sizes": sizes,
            "equal_fibers": len(set(sizes)) == 1,
            "quotient_table": quotient,
        })

    def visit(index: int, maximum_label: int) -> None:
        nonlocal truncated
        if truncated or len(decompositions) >= max_results:
            truncated = True
            return
        if index == carrier_size:
            if examined >= max_partitions:
                truncated = True
                return
            inspect_partition(maximum_label + 1)
            return
        for label in range(maximum_label + 2):
            labels[index] = label
            visit(index + 1, max(maximum_label, label))
            if truncated:
                return

    labels[0] = 0
    visit(1, 0)
    decompositions.sort(
        key=lambda row: (
            len(row["blocks"]),
            row["block_sizes"],
            row["blocks"],
        )
    )
    return {
        "kind": "CongruenceDecompositionState",
        "status": "truncated" if truncated else "complete",
        "carrier_size": carrier_size,
        "partitions_examined": examined,
        "decomposition_count": len(decompositions),
        "decompositions": decompositions,
        "recursive_interpretation": (
            "Each decomposition is a quotient node whose blocks are fibers. "
            "Repeated analysis inside quotient/fiber models yields a congruence "
            "chain; tables with no nontrivial result require a different "
            "symbolic language."
        ),
    }


def skew_product_counterexample_search(
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    config: SkewProductConfig | None = None,
) -> tuple[str, list[list[int]] | None, dict[str, Any]]:
    """Synthesize a compact Q-by-fiber extension with CEGIS.

    The quotient Q is required to satisfy H. By default it must satisfy G too,
    ensuring that any target separation is genuinely created in the fibers
    rather than inherited from a smaller quotient countermodel.
    """
    config = (config or SkewProductConfig()).normalized()
    try:
        from ortools.sat.python import cp_model
    except Exception:
        return "unavailable", None, {
            "kind": "SkewProductSearchState",
            "version": SKEW_PRODUCT_VERSION,
            "status": "unavailable",
            "reason": "ortools.sat.python.cp_model is not available",
            "config": asdict(config),
        }

    started = time.monotonic()
    deadline = started + config.time_budget
    control_size = config.control_size
    fiber_size = config.fiber_size
    carrier_size = control_size * fiber_size
    library = affine_fiber_library(
        fiber_size,
        include_order=config.fiber_library == "affine_order",
    )
    model = cp_model.CpModel()
    control = {
        (left, right): model.NewIntVar(
            0,
            control_size - 1,
            f"control_{left}_{right}",
        )
        for left in range(control_size)
        for right in range(control_size)
    }
    selectors = {
        (left, right): model.NewIntVar(
            0,
            len(library) - 1,
            f"fiber_selector_{left}_{right}",
        )
        for left in range(control_size)
        for right in range(control_size)
    }
    operation = {
        (left, right): model.NewIntVar(
            0,
            carrier_size - 1,
            f"operation_{left}_{right}",
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
                0,
                fiber_size - 1,
                f"fiber_value_{left}_{right}",
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
                == control[(left_control, right_control)] * fiber_size + fiber_value
            )

    quotient_aux = [0]
    quotient_obligation_count = 0

    def add_quotient_equation(equation: dict[str, Any], label: str) -> None:
        nonlocal quotient_obligation_count
        for values in product(
            range(control_size),
            repeat=len(equation["variables"]),
        ):
            env = dict(zip(equation["variables"], values))
            left = _cp_eval(
                model,
                equation["lhs"],
                env,
                flat_control,
                control_size,
                quotient_aux,
                f"quotient_{label}",
            )
            right = _cp_eval(
                model,
                equation["rhs"],
                env,
                flat_control,
                control_size,
                quotient_aux,
                f"quotient_{label}",
            )
            model.Add(left == right)
            quotient_obligation_count += 1

    add_quotient_equation(h_eq, "h")
    if config.require_quotient_goal:
        add_quotient_equation(g_eq, "g")

    goal_aux = [0]
    goal_env = {
        variable: model.NewIntVar(
            0,
            carrier_size - 1,
            f"goal_witness_{variable}",
        )
        for variable in g_eq["variables"]
    }
    goal_left = _cp_eval(
        model,
        g_eq["lhs"],
        goal_env,
        flat_operation,
        carrier_size,
        goal_aux,
        "goal",
    )
    goal_right = _cp_eval(
        model,
        g_eq["rhs"],
        goal_env,
        flat_operation,
        carrier_size,
        goal_aux,
        "goal",
    )
    model.Add(goal_left != goal_right)

    h_constraints: set[tuple[int, ...]] = set()
    full_aux = [0]

    def add_h_assignment(values: tuple[int, ...]) -> None:
        if values in h_constraints:
            return
        h_constraints.add(values)
        env = dict(zip(h_eq["variables"], values))
        left = _cp_eval(
            model,
            h_eq["lhs"],
            env,
            flat_operation,
            carrier_size,
            full_aux,
            "lifted_h",
        )
        right = _cp_eval(
            model,
            h_eq["rhs"],
            env,
            flat_operation,
            carrier_size,
            full_aux,
            "lifted_h",
        )
        model.Add(left == right)

    for control_values in product(
        range(control_size),
        repeat=len(h_eq["variables"]),
    ):
        add_h_assignment(
            tuple(value * fiber_size for value in control_values)
        )
    for value in range(carrier_size):
        add_h_assignment(tuple(value for _ in h_eq["variables"]))

    events: list[dict[str, Any]] = []
    last_summary: dict[str, Any] | None = None
    last_witness: dict[str, Any] | None = None
    total_checked = 0

    for iteration in range(1, config.max_iterations + 1):
        remaining = deadline - time.monotonic()
        if remaining <= 0.05:
            break
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = max(0.05, remaining)
        solver.parameters.num_search_workers = config.workers
        solver.parameters.random_seed = config.seed + iteration - 1
        cp_status = solver.Solve(model)
        status_name = solver.StatusName(cp_status)
        event: dict[str, Any] = {
            "iteration": iteration,
            "cp_status": status_name,
            "wall_time": round(float(solver.WallTime()), 3),
            "branches": int(solver.NumBranches()),
            "conflicts": int(solver.NumConflicts()),
            "lifted_h_constraints": len(h_constraints),
        }
        if cp_status == cp_model.INFEASIBLE:
            events.append(event)
            return "infeasible", None, {
                "kind": "SkewProductSearchState",
                "version": SKEW_PRODUCT_VERSION,
                "status": "family_infeasible",
                "config": asdict(config),
                "carrier_size": carrier_size,
                "fiber_library_size": len(library),
                "quotient_obligation_count": quotient_obligation_count,
                "lifted_h_constraints": len(h_constraints),
                "iterations": iteration,
                "events": events[-12:],
                "seconds": round(time.monotonic() - started, 3),
                "suggested_next_actions": [
                    _skew_to_bundle_suggestion(config),
                ],
                "need_hint": (
                    "The equal-fiber compact extension is mechanically "
                    "infeasible. Try the suggested unequal-fiber bundle, or "
                    "change the quotient/fiber sizes."
                ),
            }
        if cp_status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            event["reason"] = "solver_budget_or_unknown"
            events.append(event)
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
        witness = _goal_witness(g_eq, table, witness_env)
        last_witness = witness
        last_summary = _parameter_summary(
            solver,
            control,
            selectors,
            library,
            config,
        )
        violations, checked, complete = _find_h_violations(
            h_eq,
            table,
            limit=config.violation_batch,
            deadline=deadline,
        )
        total_checked += checked
        event.update({
            "h_assignments_checked": checked,
            "h_scan_complete": complete,
            "h_violations_found": len(violations),
            "first_h_violation": (
                dict(zip(h_eq["variables"], violations[0]))
                if violations
                else None
            ),
            "goal_witness": witness,
        })
        events.append(event)
        if complete and not violations:
            if not baby_solver.is_counterexample(h_eq, g_eq, table):
                return "internal_error", None, {
                    "kind": "SkewProductSearchState",
                    "version": SKEW_PRODUCT_VERSION,
                    "status": "verification_mismatch",
                    "events": events[-12:],
                }
            return "found", table, {
                "kind": "SkewProductSearchState",
                "version": SKEW_PRODUCT_VERSION,
                "status": "verified_countermodel",
                "config": asdict(config),
                "carrier_size": carrier_size,
                "fiber_library_size": len(library),
                "quotient_obligation_count": quotient_obligation_count,
                "lifted_h_constraints": len(h_constraints),
                "iterations": iteration,
                "h_assignments_checked_total": total_checked,
                "goal_witness": witness,
                "parameters": last_summary,
                "events": events[-12:],
                "seconds": round(time.monotonic() - started, 3),
                "need_hint": None,
            }
        if not complete and not violations:
            break
        for values in violations:
            add_h_assignment(values)

    return "budget", None, {
        "kind": "SkewProductSearchState",
        "version": SKEW_PRODUCT_VERSION,
        "status": "search_incomplete",
        "config": asdict(config),
        "carrier_size": carrier_size,
        "fiber_library_size": len(library),
        "quotient_obligation_count": quotient_obligation_count,
        "lifted_h_constraints": len(h_constraints),
        "iterations": len(events),
        "h_assignments_checked_total": total_checked,
        "last_goal_witness": last_witness,
        "last_parameters": last_summary,
        "events": events[-12:],
        "seconds": round(time.monotonic() - started, 3),
        "suggested_next_actions": [
            _skew_to_bundle_suggestion(config),
        ],
        "need_hint": (
            "The compact extension remains plausible but CEGIS did not converge. "
            "Increase the budget, change factor sizes, or try the suggested "
            "unequal-fiber bundle."
        ),
    }
