"""Structured, mechanically assembled infinite-countermodel action contract."""

from __future__ import annotations

import re
import textwrap
from copy import deepcopy
from typing import Any


INFINITE_MODEL_PLAN_VERSION = "sair-infinite-model-plan-v1"
PLAN_KINDS = {"infinite_model_plan", "structured_infinite_model"}
PATCH_KINDS = {"infinite_model_patch", "structured_infinite_model_patch"}
PART_FIELDS = (
    "carrier",
    "operation",
    "setup",
    "hypothesis_proof",
    "counterexample_proof",
)
_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
_IMPORT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")
_BANNED = re.compile(
    r"\b(?:sorry|admit|axiom|unsafe|def\s+submission)\b|<(?!;>)[A-Za-z][^>\n]{0,79}>",
    re.IGNORECASE,
)


def is_infinite_model_plan(action: Any) -> bool:
    return isinstance(action, dict) and str(action.get("kind") or "") in PLAN_KINDS


def is_infinite_model_patch(action: Any) -> bool:
    return isinstance(action, dict) and str(action.get("kind") or "") in PATCH_KINDS


def _fragment(value: Any, *, field: str, limit: int) -> tuple[str | None, str | None]:
    if not isinstance(value, str) or not value.strip():
        return None, f"{field} must be a nonempty Lean fragment"
    text = value.strip()
    if len(text.encode("utf-8")) > limit:
        return None, f"{field} exceeds {limit} bytes"
    match = _BANNED.search(text)
    if match:
        return None, f"{field} contains disallowed placeholder/declaration: {match.group(0)}"
    return text, None


def _normalize_tactic_fragment(text: str) -> tuple[str, list[str]]:
    """Repair common outer indentation without rewriting Lean syntax."""
    repairs: list[str] = []
    lines = text.strip().splitlines()
    if lines and lines[0].strip() == "by":
        lines = lines[1:]
        repairs.append("removed_redundant_outer_by")
        indents = [
            len(line) - len(line.lstrip())
            for line in lines
            if line.strip()
        ]
        baseline = min(indents) if indents else 0
        lines = textwrap.dedent("\n".join(lines)).splitlines()
        if baseline > 0:
            repairs.append(f"dedented_following_tactics_by_{baseline}")
    if len(lines) > 1:
        indents = [
            len(line) - len(line.lstrip())
            for line in lines[1:]
            if line.strip()
        ]
        baseline = min(indents) if indents else 0
        if baseline > 0:
            lines = [lines[0]] + [
                line[baseline:] if line.strip() else line
                for line in lines[1:]
            ]
            repairs.append(f"dedented_following_tactics_by_{baseline}")
    return "\n".join(lines).strip(), repairs


def normalize_infinite_model_plan(
    action: dict[str, Any],
) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    """Validate the piece envelope without trusting any mathematical claim."""
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
    plan = {
        "kind": "infinite_model_plan",
        "version": INFINITE_MODEL_PLAN_VERSION,
        "model_name": str(source.get("model_name") or "model").strip(),
        "imports": list(raw_imports) if isinstance(raw_imports, list) else raw_imports,
        "carrier": source.get("carrier"),
        "operation": source.get("operation"),
        "setup": list(raw_setup) if isinstance(raw_setup, list) else raw_setup,
        "hypothesis_proof": source.get("hypothesis_proof"),
        "counterexample_proof": source.get("counterexample_proof"),
    }
    errors: list[dict[str, Any]] = []
    if not _NAME_RE.fullmatch(plan["model_name"]):
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
        if not _IMPORT_RE.fullmatch(name):
            errors.append({"field": "imports", "message": f"invalid import name: {name}"})
        elif name != "JudgeProblem" and name not in normalized_imports:
            normalized_imports.append(name)
    plan["imports"] = normalized_imports

    completed: list[str] = []
    missing: list[str] = []
    syntax_repairs: list[dict[str, Any]] = []
    for field, limit in (
        ("carrier", 500),
        ("operation", 5_000),
        ("hypothesis_proof", 8_000),
        ("counterexample_proof", 8_000),
    ):
        value = plan.get(field)
        if value in (None, ""):
            missing.append(field)
            continue
        fragment, error = _fragment(value, field=field, limit=limit)
        if error:
            errors.append({"field": field, "message": error})
        else:
            if field in {"hypothesis_proof", "counterexample_proof"}:
                fragment, repairs = _normalize_tactic_fragment(fragment)
                syntax_repairs.extend(
                    {"field": field, "repair": repair}
                    for repair in repairs
                )
            plan[field] = fragment
            completed.append(field)

    if not isinstance(plan["setup"], list):
        errors.append({"field": "setup", "message": "setup must be a list of Lean fragments"})
        plan["setup"] = []
    elif len(plan["setup"]) > 16:
        errors.append({"field": "setup", "message": "at most 16 setup fragments are allowed"})
    normalized_setup = []
    for index, value in enumerate(plan["setup"][:16]):
        fragment, error = _fragment(value, field=f"setup[{index}]", limit=5_000)
        if error:
            errors.append({"field": f"setup[{index}]", "message": error})
        else:
            normalized_setup.append(fragment)
    plan["setup"] = normalized_setup
    if normalized_setup:
        completed.append("setup")
    elif "setup" not in missing:
        completed.append("setup")

    state = {
        "kind": "InfiniteModelPlanState",
        "version": INFINITE_MODEL_PLAN_VERSION,
        "status": "invalid_plan" if errors else ("missing_parts" if missing else "plan_ready"),
        "completed_parts": completed,
        "missing_parts": missing,
        "errors": errors,
        "schema_repairs": schema_repairs,
        "syntax_repairs": syntax_repairs,
        "part_count": len(completed),
        "total_parts": len(PART_FIELDS),
        "need_hint": (
            "Repair the listed Lean fragment envelope errors."
            if errors
            else (
                f"Provide the missing structured parts: {', '.join(missing)}."
                if missing
                else "The plan is complete; assemble it and use Lean diagnostics for repairs."
            )
        ),
        "trust_boundary": (
            "Structured parts remain untrusted until the mechanically assembled "
            "submission is accepted by the Lean judge."
        ),
    }
    return (None if errors else plan), state


def merge_infinite_model_patch(
    base: dict[str, Any],
    patch: dict[str, Any],
) -> dict[str, Any]:
    """Apply an explicit field patch while preserving every unmentioned part."""
    source = base.get("plan") if isinstance(base.get("plan"), dict) else base
    merged = deepcopy(source)
    updates = patch.get("set") if isinstance(patch.get("set"), dict) else patch
    for field in (
        "model_name",
        "imports",
        "carrier",
        "operation",
        "setup",
        "hypothesis_proof",
        "counterexample_proof",
    ):
        if field in updates:
            merged[field] = deepcopy(updates[field])
    merged["kind"] = "infinite_model_plan"
    merged["version"] = INFINITE_MODEL_PLAN_VERSION
    return merged


def _indent(fragment: str, spaces: int) -> str:
    prefix = " " * spaces
    return "\n".join(prefix + line if line.strip() else line for line in fragment.splitlines())


def assemble_infinite_model_plan(
    action: dict[str, Any],
) -> tuple[str | None, dict[str, Any]]:
    plan, state = normalize_infinite_model_plan(action)
    if plan is None or state["status"] != "plan_ready":
        return None, state
    imports = "\n".join(f"import {name}" for name in plan["imports"])
    setup = ""
    if plan["setup"]:
        setup = "\n" + "\n".join(_indent(fragment, 2) for fragment in plan["setup"])
    code = (
        f"{imports}\n\n"
        "def submission : Goal := by\n"
        f"  let {plan['model_name']} : Magma {plan['carrier']} := "
        f"⟨{plan['operation']}⟩\n"
        f"  use {plan['carrier']}, {plan['model_name']}"
        f"{setup}\n"
        "  constructor\n"
        f"  · {_indent(plan['hypothesis_proof'], 4).lstrip()}\n"
        f"  · {_indent(plan['counterexample_proof'], 4).lstrip()}\n"
    )
    ready_state = {
        **state,
        "status": "candidate_ready",
        "artifact_bytes": len(code.encode("utf-8")),
        "assembly": {
            "model_name": plan["model_name"],
            "carrier": plan["carrier"],
            "import_count": len(plan["imports"]),
            "setup_count": len(plan["setup"]),
        },
        "need_hint": None,
    }
    return code, ready_state
