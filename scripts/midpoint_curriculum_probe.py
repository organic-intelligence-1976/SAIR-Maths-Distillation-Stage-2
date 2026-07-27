#!/usr/bin/env python3
"""Build and probe an LLM midpoint curriculum.

The goal is item 3: create an artificial frontier where a weak mechanical view
is stuck, a known bad midpoint fails, and a known good midpoint/chain succeeds.
The resulting artifacts become few-shot examples for teaching System 2 how to
extend System 1's reach.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "official-stage2"))

import baby_solver as solver  # noqa: E402
from curriculum_blackboard import LemmaBlackboard  # noqa: E402
from feedback_uptake_probe import call_chat, load_config  # noqa: E402

try:  # noqa: E402
    from judge.verify import (  # type: ignore
        JudgeConfig,
        JudgeConfigurationError,
        JudgeInfrastructureError,
        _resolve_config,
        verify_answer,
    )
except Exception:  # pragma: no cover - local judge is optional for artifact generation
    JudgeConfig = None  # type: ignore
    JudgeConfigurationError = Exception  # type: ignore
    JudgeInfrastructureError = Exception  # type: ignore
    _resolve_config = None  # type: ignore
    verify_answer = None  # type: ignore

try:  # noqa: E402
    from pipeline.proxy import DEFAULT_PROOF_POLICY  # type: ignore
except Exception:  # pragma: no cover - keep judge probes usable without proxy deps
    DEFAULT_PROOF_POLICY = {
        "allowed_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "allowed_declarations": ["letFun"],
        "allowed_declaration_prefixes": [
            "And.", "Bool.", "Classical.", "Decidable.", "Eq.",
            "EquationLHS", "EquationRHS", "Goal",
            "Exists.", "False.",
            "Fin.", "Fintype.", "Function.", "HEq.", "Iff.", "Init.", "Int.", "Lean.",
            "List.", "Magma.", "Mathlib.", "MemoFinOp.", "Nat.", "Nonempty.", "Not.",
            "NthRewrites.", "OfNat.", "Option.", "Or.", "Prod.", "PUnit.",
            "RewriteCombinations.", "RewriteGoal.", "RewriteHypothesis.",
            "RewriteHypothesisAndGoal.", "SimpleRewrites.",
            "Std.", "Subgraph.", "Subtype.", "Sum.",
            "Trans.", "True.", "Unit.",
            "JudgeDecide.", "JudgeFinOp.", "JudgeMagma.",
            "inst", "of_decide_", "submission.",
            "congrArg", "congr_arg", "eq_self", "of_eq_true", "id",
            "eq_comm", "eq_mp", "eq_mpr", "rfl", "absurd",
        ],
    }


GOOD_OPCONST = {
    "kind": "midpoint",
    "lemma": "a ◇ b = c ◇ d",
    "why": "rowconst is too narrow; derived opconst-like equations suggest the stronger direct bridge",
}

BAD_GOAL_SPECIFIC_OPCONST = {
    "kind": "tool_call",
    "tool": "lemma_hint",
    "target": "goal",
    "lemmas": [
        {
            "equation": "(y ◇ x) = ((w ◇ y) ◇ y)",
            "seed_h_args": [["y", "x", "y"]],
        }
    ],
    "why": "too goal-specific; plausible-looking bridge but hard to prove from H",
}

BAD_SQUARE_CONST = {
    "kind": "tool_call",
    "tool": "lemma_hint",
    "target": "goal",
    "lemmas": [{"equation": "a ◇ a = b ◇ b"}],
    "why": "too weak/incomplete when feedback shows full opconst-like collapse",
}

GOOD_RIGHT_SQUARE_CHAIN = {
    "kind": "tool_call",
    "tool": "lemma_chain",
    "target": "goal",
    "lemmas": [
        {"name": "square_absorb", "equation": "u ◇ (v ◇ v) = v"},
        {"name": "right_square", "equation": "u ◇ v = v ◇ v"},
    ],
}

FULL_RIGHT_SQUARE_ACTION = {
    "kind": "tool_call",
    "tool": "right_square_chain",
    "target": "goal",
}

FULL_SQUARE_SANDWICH_ACTION = {
    "kind": "tool_call",
    "tool": "square_sandwich_chain",
    "target": "goal",
}

BAD_RIGHT_SQUARE_INCOMPLETE = {
    "kind": "tool_call",
    "tool": "lemma_chain",
    "target": "goal",
    "lemmas": [{"name": "square_absorb", "equation": "u ◇ (v ◇ v) = v"}],
    "why": "one helper can be true but not enough to consume the goal",
}

GOOD_SQUARE_SANDWICH_CHAIN = {
    "kind": "tool_call",
    "tool": "lemma_chain",
    "target": "goal",
    "lemmas": [
        {"name": "square_const", "equation": "u ◇ u = v ◇ v"},
        {"name": "right_id_square", "equation": "u ◇ (v ◇ v) = u"},
        {"name": "sandwich", "equation": "(v ◇ u) ◇ v = u"},
        {"name": "left_sandwich", "equation": "v ◇ (u ◇ v) = u"},
    ],
}

BAD_SQUARE_SANDWICH_INCOMPLETE = {
    "kind": "tool_call",
    "tool": "lemma_chain",
    "target": "goal",
    "lemmas": [
        {"name": "square_const", "equation": "u ◇ u = v ◇ v"},
        {"name": "right_id_square", "equation": "u ◇ (v ◇ v) = u"},
    ],
    "why": "gets the square constant/right identity ideas but misses the sandwich step needed for the goal",
}

BAD_SQUARE_SANDWICH_GOAL_AS_MIDPOINT = {
    "kind": "midpoint",
    "lemma": "x = (y ◇ (x ◇ (y ◇ x))) ◇ x",
    "why": "repeats the held-out goal as a midpoint instead of proposing reusable helper lemmas",
}

BAD_ROWCONST_ONLY_CHAIN = {
    "kind": "tool_call",
    "tool": "lemma_chain",
    "target": "goal",
    "lemmas": [{"name": "rowconst", "equation": "a ◇ b = a ◇ c"}],
    "why": "rowconst can be true but not enough to consume the goal",
}

GOOD_ROWCONST_OPCONST_CHAIN = {
    "kind": "tool_call",
    "tool": "lemma_chain",
    "target": "goal",
    "lemmas": [
        {"name": "rowconst", "equation": "a ◇ b = a ◇ c"},
        {"name": "opconst", "equation": "a ◇ b = c ◇ d"},
    ],
    "why": "proved rowconst did not close the goal; opconst is the stronger reusable bridge",
}

BAD_PROJ_L_ONLY_CHAIN = {
    "kind": "tool_call",
    "tool": "lemma_chain",
    "target": "goal",
    "lemmas": [{"name": "proj_l", "equation": "a ◇ b = a"}],
    "why": "left projection alone can be true but still leave the goal disconnected",
}

BAD_PROJ_R_ONLY_CHAIN = {
    "kind": "tool_call",
    "tool": "lemma_chain",
    "target": "goal",
    "lemmas": [{"name": "proj_r", "equation": "a ◇ b = b"}],
    "why": "right projection alone can be true but still leave the goal disconnected",
}

GOOD_PROJECTION_PAIR_CHAIN = {
    "kind": "tool_call",
    "tool": "lemma_chain",
    "target": "goal",
    "lemmas": [
        {"name": "proj_l", "equation": "a ◇ b = a"},
        {"name": "proj_r", "equation": "a ◇ b = b"},
    ],
    "why": "one projection proved but was not consumed; adding the opposite projection collapses all products to both arguments and lets the graph close",
}

BAD_PROJECTION_GOAL_SPECIFIC_MIDPOINT = {
    "kind": "midpoint",
    "lemma": "((x ◇ w) ◇ w) = ((y ◇ w) ◇ w)",
    "why": "proved goal-specific closest-pair bridge but did not consume the goal; projection feedback needs reusable projection lemmas instead",
}


CURRICULUM: dict[str, dict[str, Any]] = {
    "opconst_train_hard1_0034": {
        "problem_id": "hard1_0034",
        "family": "opconst_from_rowconst_failure",
        "role": "train",
        "diagnostic_tool": {
            "kind": "tool_call",
            "tool": "standard_aux_superposition",
            "target": "goal",
            "lemmas": ["rowconst"],
            "budget": 3,
        },
        "bad_actions": [BAD_GOAL_SPECIFIC_OPCONST, BAD_SQUARE_CONST],
        "good_action": GOOD_OPCONST,
        "lesson": (
            "When rowconst is stuck but shape_diagnostics contains opconst_like "
            "rows such as (v0 ◇ v1) = (v2 ◇ v3), propose the stronger universal "
            "midpoint a ◇ b = c ◇ d instead of a goal-specific equality."
        ),
    },
    "opconst_holdout_hard1_0046": {
        "problem_id": "hard1_0046",
        "family": "opconst_from_rowconst_failure",
        "role": "holdout",
        "diagnostic_tool": {
            "kind": "tool_call",
            "tool": "standard_aux_superposition",
            "target": "goal",
            "lemmas": ["rowconst"],
            "budget": 3,
        },
        "bad_actions": [BAD_SQUARE_CONST],
        "good_action": GOOD_OPCONST,
        "lesson": "Same opconst repair should transfer from hard1_0034.",
    },
    "opconst_holdout_hard2_0065": {
        "problem_id": "hard2_0065",
        "family": "opconst_from_rowconst_failure",
        "role": "holdout",
        "diagnostic_tool": {
            "kind": "tool_call",
            "tool": "standard_aux_superposition",
            "target": "goal",
            "lemmas": ["rowconst"],
            "budget": 3,
        },
        "bad_actions": [BAD_SQUARE_CONST],
        "good_action": GOOD_OPCONST,
        "lesson": "Same opconst repair should transfer across hard-file families.",
    },
    "right_square_train_hard2_0107": {
        "problem_id": "hard2_0107",
        "family": "right_square_chain",
        "role": "train",
        "diagnostic_tool": None,
        "bad_actions": [BAD_RIGHT_SQUARE_INCOMPLETE],
        "good_action": GOOD_RIGHT_SQUARE_CHAIN,
        "capability_experiment": {
            "full_mechanical_action": FULL_RIGHT_SQUARE_ACTION,
            "curriculum_mask": {"disabled": ["tool:right_square_chain"]},
            "negative_control_mask": {
                "disabled": [
                    "tool:right_square_chain",
                    "primitive:generic_midpoint_prover",
                ]
            },
        },
        "lesson": (
            "For right-square absorption, one helper is often not enough. The "
            "mechanical consumer wants the chain u ◇ (v ◇ v) = v and "
            "u ◇ v = v ◇ v."
        ),
    },
    "square_sandwich_train_hard1_0018": {
        "problem_id": "hard1_0018",
        "family": "square_sandwich_chain",
        "role": "train",
        "diagnostic_tool": None,
        "bad_actions": [BAD_SQUARE_SANDWICH_INCOMPLETE],
        "good_action": GOOD_SQUARE_SANDWICH_CHAIN,
        "capability_experiment": {
            "full_mechanical_action": FULL_SQUARE_SANDWICH_ACTION,
            "curriculum_mask": {"disabled": ["tool:square_sandwich_chain"]},
            "negative_control_mask": {
                "disabled": [
                    "tool:square_sandwich_chain",
                    "primitive:generic_midpoint_prover",
                ]
            },
        },
        "lesson": (
            "For square-sandwich hypotheses, square_const and right_id_square "
            "are only the start; include sandwich and often left_sandwich."
        ),
    },
    "square_sandwich_holdout_hard3_0231": {
        "problem_id": "hard3_0231",
        "family": "square_sandwich_chain",
        "role": "holdout",
        "diagnostic_tool": None,
        "bad_actions": [BAD_SQUARE_SANDWICH_GOAL_AS_MIDPOINT, BAD_SQUARE_SANDWICH_INCOMPLETE],
        "good_action": GOOD_SQUARE_SANDWICH_CHAIN,
        "capability_experiment": {
            "full_mechanical_action": FULL_SQUARE_SANDWICH_ACTION,
            "curriculum_mask": {"disabled": ["tool:square_sandwich_chain"]},
            "negative_control_mask": {
                "disabled": [
                    "tool:square_sandwich_chain",
                    "primitive:generic_midpoint_prover",
                ]
            },
        },
        "lesson": (
            "Same square-sandwich helper chain transfers to a different goal "
            "under the same H: square_const/right_id alone is not enough; add "
            "sandwich and left_sandwich. Do not repeat the goal itself as a "
            "midpoint; that asks the mechanical side to solve the original "
            "hard problem."
        ),
    },
    "rowconst_opconst_train_hard1_0013": {
        "problem_id": "hard1_0013",
        "family": "proved_rowconst_needs_opconst",
        "role": "train",
        "diagnostic_tool": BAD_ROWCONST_ONLY_CHAIN,
        "bad_actions": [BAD_ROWCONST_ONLY_CHAIN],
        "good_action": GOOD_ROWCONST_OPCONST_CHAIN,
        "lesson": (
            "If rowconst `(a ◇ b) = (a ◇ c)` is proved but not consumed, do not "
            "stop there. Add the stronger opconst bridge `a ◇ b = c ◇ d`; the "
            "mechanical side can prove opconst from H plus rowconst and then "
            "consume the goal."
        ),
    },
    "rowconst_opconst_holdout_hard2_0155": {
        "problem_id": "hard2_0155",
        "family": "proved_rowconst_needs_opconst",
        "role": "holdout",
        "diagnostic_tool": BAD_ROWCONST_ONLY_CHAIN,
        "bad_actions": [BAD_ROWCONST_ONLY_CHAIN],
        "good_action": GOOD_ROWCONST_OPCONST_CHAIN,
        "lesson": "Same rowconst-to-opconst repair transfers to a different goal under the same H.",
    },
    "rowconst_opconst_holdout_hard2_0198": {
        "problem_id": "hard2_0198",
        "family": "proved_rowconst_needs_opconst",
        "role": "holdout",
        "diagnostic_tool": BAD_ROWCONST_ONLY_CHAIN,
        "bad_actions": [BAD_ROWCONST_ONLY_CHAIN],
        "good_action": GOOD_ROWCONST_OPCONST_CHAIN,
        "lesson": "Same proved-but-not-consumed rowconst feedback should be repaired by adding opconst.",
    },
    "projection_pair_holdout_hard2_0004": {
        "problem_id": "hard2_0004",
        "family": "projection_pair",
        "role": "holdout",
        "diagnostic_tool": BAD_PROJ_L_ONLY_CHAIN,
        "bad_actions": [BAD_PROJ_L_ONLY_CHAIN, BAD_PROJ_R_ONLY_CHAIN, BAD_PROJECTION_GOAL_SPECIFIC_MIDPOINT],
        "good_action": GOOD_PROJECTION_PAIR_CHAIN,
        "lesson": (
            "If one projection lemma is proved but not consumed, try the opposite "
            "projection too. For this case, `a ◇ b = a` alone and `a ◇ b = b` "
            "alone both fail to close the goal, but the pair `proj_l` plus "
            "`proj_r` is mechanically proved and consumed. Do not chase a "
            "goal-specific closest-pair midpoint when projection-shaped feedback "
            "is visible."
        ),
    },
}


def iter_problem_rows() -> list[dict[str, Any]]:
    paths = [
        ROOT / "official-stage2" / "examples" / "problems" / "hard1.jsonl",
        ROOT / "official-stage2" / "examples" / "problems" / "hard2.jsonl",
        ROOT / "official-stage2" / "examples" / "problems" / "hard3.jsonl",
        ROOT / "official-stage2" / "examples" / "problems" / "normal.jsonl",
        ROOT / ".artifacts" / "true_llm_probe.jsonl",
        ROOT / ".artifacts" / "collab_targeted.jsonl",
        ROOT / ".artifacts" / "reference_aux_probe.jsonl",
    ]
    rows: list[dict[str, Any]] = []
    seen: set[str] = set()
    for path in paths:
        if not path.exists():
            continue
        with path.open("r", encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                row = json.loads(line)
                pid = str(row.get("id") or "")
                if pid and pid not in seen:
                    rows.append(row)
                    seen.add(pid)
    return rows


def problem_by_id(problem_id: str) -> dict[str, Any]:
    for row in iter_problem_rows():
        if row.get("id") == problem_id:
            return row
    raise KeyError(f"problem id not found: {problem_id}")


def alpha_rename_equation(text: str, mapping: dict[str, str]) -> str:
    if len(set(mapping.values())) != len(mapping) or any(not re.fullmatch(r"[a-z]", value) for value in mapping.values()):
        raise ValueError("alpha-renaming must map to distinct single lowercase letters")
    return re.sub(r"\b([a-z])\b", lambda match: mapping.get(match.group(1), match.group(1)), text)


def discover_family_candidates(family: str, max_rows: int | None = None) -> dict[str, Any]:
    """Find likely curriculum holdouts using cheap shape filters only.

    This deliberately avoids the generic lemma-chain consumer on every row. The
    expensive consumer should only be used after this prefilter produces a tiny
    shortlist.
    """
    if family == "right_square_chain":
        predicate = lambda h_eq, g_eq: bool(solver.right_square_h_roles(h_eq))
        focused_body = solver.generic_right_square_chain_body
    elif family == "square_sandwich_chain":
        predicate = lambda h_eq, g_eq: bool(solver.square_sandwich_h_roles(h_eq))
        focused_body = solver.square_sandwich_chain_body
    else:
        raise ValueError(f"unsupported discovery family: {family}")

    known_problem_ids = {spec["problem_id"] for spec in CURRICULUM.values()}
    shaped: list[dict[str, Any]] = []
    focused_hits: list[dict[str, Any]] = []
    rows = [row for row in iter_problem_rows() if row.get("answer") is True]
    if max_rows is not None:
        rows = rows[:max_rows]
    started = time.monotonic()
    for row in rows:
        h_eq = solver.parse_equation(row["equation1"])
        g_eq = solver.parse_equation(row["equation2"])
        if not predicate(h_eq, g_eq):
            continue
        entry = {
            "id": row.get("id"),
            "h": row.get("equation1"),
            "goal": row.get("equation2"),
            "already_in_curriculum": row.get("id") in known_problem_ids,
        }
        shaped.append(entry)
        if focused_body(h_eq, g_eq):
            focused_hits.append(entry)
    return {
        "family": family,
        "rows_scanned": len(rows),
        "shaped_count": len(shaped),
        "focused_hit_count": len(focused_hits),
        "new_focused_hits": [row for row in focused_hits if not row["already_in_curriculum"]],
        "shaped": shaped,
        "focused_hits": focused_hits,
        "seconds": round(time.monotonic() - started, 3),
    }


def compact_json(value: Any, limit: int = 2400) -> str:
    text = json.dumps(value, ensure_ascii=False, sort_keys=True)
    return text if len(text) <= limit else text[: limit - 3] + "..."


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def public_llm_config(config: dict[str, Any]) -> dict[str, Any]:
    llm = config.get("llm") if isinstance(config.get("llm"), dict) else {}
    return {
        key: llm.get(key)
        for key in (
            "model",
            "base_url",
            "provider",
            "temperature",
            "max_output_tokens",
            "reasoning_effort",
        )
        if llm.get(key) is not None
    }


def short_text(value: Any, limit: int = 1200) -> str:
    text = "" if value is None else str(value)
    return text if len(text) <= limit else text[: limit - 3] + "..."


def to_judge_problem(problem: dict[str, Any]) -> dict[str, Any]:
    out = {
        "id": problem["id"],
        "eq1_id": problem["eq1_id"],
        "eq2_id": problem["eq2_id"],
        "equation1": problem["equation1"],
        "equation2": problem["equation2"],
    }
    if problem.get("proof_policy"):
        out["proof_policy"] = problem["proof_policy"]
    elif DEFAULT_PROOF_POLICY is not None:
        out["proof_policy"] = DEFAULT_PROOF_POLICY
    return out


def judge_true_body(problem: dict[str, Any], body: str | None, timeout_seconds: int) -> dict[str, Any]:
    if not body:
        return {"status": "no_body", "accepted": False}
    if verify_answer is None or _resolve_config is None or JudgeConfig is None:
        return {
            "status": "judge_unavailable",
            "accepted": False,
            "message": "official-stage2 judge imports were unavailable",
        }
    started = time.monotonic()
    try:
        base = _resolve_config(None)
        config = JudgeConfig(
            lake_bin=base.lake_bin,
            lean_bin=base.lean_bin,
            artifact_dir=base.artifact_dir,
            lean_timeout_seconds=max(1, int(timeout_seconds)),
            max_code_length=base.max_code_length,
            max_false_cert_bytes=base.max_false_cert_bytes,
        )
        raw_answer = json.dumps({
            "verdict": "true",
            "code": solver.make_true_code(body),
        })
        result = verify_answer(to_judge_problem(problem), raw_answer, config=config)
    except JudgeInfrastructureError as exc:
        return {
            "status": "judge_infrastructure_error",
            "accepted": False,
            "message": short_text(exc),
            "seconds": round(time.monotonic() - started, 3),
        }
    except JudgeConfigurationError as exc:
        return {
            "status": "judge_configuration_error",
            "accepted": False,
            "message": short_text(exc),
            "seconds": round(time.monotonic() - started, 3),
        }
    status = str(result.get("status") or "unknown")
    return {
        "status": status,
        "accepted": status == "accepted",
        "message": short_text(result.get("message")),
        "stderr": short_text(result.get("stderr"), 1600),
        "direct_declarations": result.get("direct_declarations"),
        "axioms": result.get("axioms"),
        "seconds": round(time.monotonic() - started, 3),
    }


def summarize_state(state: dict[str, Any] | None) -> dict[str, Any]:
    if not isinstance(state, dict):
        return {}
    summary = {
        "kind": state.get("kind"),
        "status": state.get("status"),
        "need_hint": state.get("need_hint"),
        "suggested_next_actions": state.get("suggested_next_actions"),
        "required_capabilities": state.get("required_capabilities"),
        "blocked_capabilities": state.get("blocked_capabilities"),
        "capability_mask": state.get("capability_mask"),
        "focused_fallbacks_withheld": state.get("focused_fallbacks_withheld"),
    }
    if state.get("kind") == "StandardAuxSuperpositionState":
        attempts = []
        for attempt in state.get("attempts") or []:
            proof_state = attempt.get("proof_state") if isinstance(attempt, dict) else None
            attempts.append({
                "kind": attempt.get("kind"),
                "status": attempt.get("status"),
                "equation": attempt.get("equation"),
                "target_shape": (proof_state or {}).get("target_shape"),
                "rowconst_diagnostics": (proof_state or {}).get("rowconst_diagnostics"),
                "shape_diagnostics": (proof_state or {}).get("shape_diagnostics", [])[:3],
                "need_hint": (proof_state or {}).get("need_hint"),
            })
        summary["attempts"] = attempts
    if state.get("kind") == "midpoint_chain_attempt":
        summary["proposed_lemmas"] = state.get("proposed_lemmas")
        summary["proved_lemmas"] = state.get("proved_lemmas")
        failures = []
        for failure in state.get("failed_midpoints") or []:
            search_state = failure.get("search_state") if isinstance(failure, dict) else None
            failures.append({
                "stage": failure.get("stage"),
                "equation": failure.get("equation"),
                "failure": failure.get("failure"),
                "target_shape": ((search_state or {}).get("superposition_state") or {}).get("target_shape"),
                "need_hint": (search_state or {}).get("need_hint"),
                "suggested_next_actions": (search_state or {}).get("suggested_next_actions"),
                "closest_pairs": (search_state or {}).get("closest_pairs", [])[:3],
            })
        summary["failed_midpoints"] = failures
        summary["goal_search_state"] = summarize_state(state.get("goal_search_state"))
    if state.get("kind") == "SearchState":
        summary.update({
            "target": state.get("target"),
            "left_component_size": state.get("left_component_size"),
            "right_component_size": state.get("right_component_size"),
            "closest_pairs": state.get("closest_pairs", [])[:4],
            "left_frontier": state.get("left_frontier", [])[:4],
            "right_frontier": state.get("right_frontier", [])[:4],
        })
    return {k: v for k, v in summary.items() if v not in (None, [], {})}


def run_action_body(
    action: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    *,
    capability_mask: Any = None,
) -> tuple[str | None, dict[str, Any] | None]:
    normalized, adapter_state = solver.normalize_llm_action(action)
    if normalized is None:
        return None, adapter_state
    if solver.is_hint_payload(normalized):
        hint_tool = solver.capability_tool_for_action(normalized)
        gate_state = solver.capability_gate_state(hint_tool, capability_mask)
        if gate_state is not None:
            return None, gate_state
        body, state = solver.hint_payload_attempt(
            normalized,
            h_eq,
            g_eq,
            capability_mask=capability_mask,
        )
        return body, state
    if normalized.get("kind") == "tool_call":
        body, state = solver.run_tool_call_detailed(
            normalized,
            h_eq,
            g_eq,
            capability_mask=capability_mask,
        )
        return body, state
    return None, {
        "kind": "UnsupportedCurriculumAction",
        "status": "unsupported",
        "action": normalized,
    }


def run_action(action: dict[str, Any], h_eq: dict[str, Any], g_eq: dict[str, Any]) -> tuple[bool, dict[str, Any] | None]:
    body, state = run_action_body(action, h_eq, g_eq)
    return bool(body), state


def baseline_state(h_eq: dict[str, Any], g_eq: dict[str, Any], h_limit: int, lemma_limit: int, congruence_cap: int) -> dict[str, Any]:
    return solver.graph_search_state(
        h_eq,
        g_eq,
        h_limit=h_limit,
        lemma_limit=lemma_limit,
        congruence_cap=congruence_cap,
        status="artificial_frontier_stuck",
    )


def capability_mode_result(
    problem: dict[str, Any],
    action: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    capability_mask: Any,
    args: argparse.Namespace,
) -> dict[str, Any]:
    started = time.monotonic()
    body, state = run_action_body(
        action,
        h_eq,
        g_eq,
        capability_mask=capability_mask,
    )
    judge = judge_true_body(problem, body, args.judge_timeout) if args.verify_judge else None
    return {
        "action": action,
        "capability_mask": solver.normalize_capability_mask(capability_mask),
        "manifest": solver.capability_manifest(capability_mask),
        "body_built": bool(body),
        "judge": judge,
        "judge_accepted": None if judge is None else bool(judge.get("accepted")),
        "state": summarize_state(state),
        "seconds": round(time.monotonic() - started, 3),
    }


def run_paired_capability_modes(
    problem: dict[str, Any],
    spec: dict[str, Any],
    h_eq: dict[str, Any],
    g_eq: dict[str, Any],
    args: argparse.Namespace,
) -> dict[str, Any] | None:
    experiment = spec.get("capability_experiment")
    if not isinstance(experiment, dict):
        return None
    full_action = experiment["full_mechanical_action"]
    curriculum_mask = experiment["curriculum_mask"]
    negative_mask = experiment["negative_control_mask"]
    full = capability_mode_result(problem, full_action, h_eq, g_eq, None, args)
    shortcut_withheld = capability_mode_result(
        problem,
        full_action,
        h_eq,
        g_eq,
        curriculum_mask,
        args,
    )
    curriculum_recovery = capability_mode_result(
        problem,
        spec["good_action"],
        h_eq,
        g_eq,
        curriculum_mask,
        args,
    )
    negative_control = capability_mode_result(
        problem,
        spec["good_action"],
        h_eq,
        g_eq,
        negative_mask,
        args,
    )
    attribution = {
        "full_mechanical_baseline_succeeds": full["body_built"],
        "shortcut_is_actually_withheld": not shortcut_withheld["body_built"] and shortcut_withheld["state"].get("status") == "withheld_for_curriculum",
        "generic_recovery_succeeds_under_withholding": curriculum_recovery["body_built"],
        "negative_control_removes_recovery": not negative_control["body_built"],
    }
    attribution["intervention_behaves_as_designed"] = all(attribution.values())
    return {
        "experiment": "full_vs_curriculum_withheld_vs_negative_control",
        "interpretation_limit": (
            "This replay proves that the proposed lemma chain can compensate for the "
            "withheld shortcut. It does not by itself prove that a live LLM can discover the chain."
        ),
        "full_mechanical": full,
        "withheld_shortcut_check": shortcut_withheld,
        "curriculum_recovery": curriculum_recovery,
        "negative_control": negative_control,
        "attribution": attribution,
    }


def run_case(case_id: str, spec: dict[str, Any], args: argparse.Namespace) -> dict[str, Any]:
    problem = problem_by_id(spec["problem_id"])
    h_eq = solver.parse_equation(problem["equation1"])
    g_eq = solver.parse_equation(problem["equation2"])
    started = time.monotonic()
    base_state = baseline_state(h_eq, g_eq, args.baseline_h_limit, args.baseline_lemma_limit, args.baseline_congruence_cap)

    diagnostic_action = spec.get("diagnostic_tool")
    diagnostic_body_text = None
    diagnostic_body = False
    diagnostic_state = None
    if diagnostic_action:
        diagnostic_body_text, diagnostic_state = run_action_body(diagnostic_action, h_eq, g_eq)
        diagnostic_body = bool(diagnostic_body_text)

    bad_results = []
    for action in spec.get("bad_actions") or []:
        if diagnostic_action is not None and action == diagnostic_action:
            body_text, state = diagnostic_body_text, diagnostic_state
        else:
            body_text, state = run_action_body(action, h_eq, g_eq)
        judge = judge_true_body(problem, body_text, args.judge_timeout) if args.verify_judge else None
        bad_results.append({
            "action": action,
            "body_built": bool(body_text),
            "judge": judge,
            "judge_accepted": None if judge is None else bool(judge.get("accepted")),
            "state": summarize_state(state),
            "raw_state": state if args.keep_raw_states else None,
        })

    good_body_text, good_state = run_action_body(spec["good_action"], h_eq, g_eq)
    good_judge = judge_true_body(problem, good_body_text, args.judge_timeout) if args.verify_judge else None
    capability_modes = run_paired_capability_modes(problem, spec, h_eq, g_eq, args) if args.paired_capability_modes else None
    fewshot = build_fewshot(
        case_id,
        problem,
        spec,
        base_state,
        diagnostic_state,
        bad_results,
        bool(good_body_text),
        good_state,
        good_judge,
    )
    return {
        "case_id": case_id,
        "problem_id": spec["problem_id"],
        "family": spec["family"],
        "role": spec.get("role"),
        "h": problem["equation1"],
        "goal": problem["equation2"],
        "baseline": summarize_state(base_state),
        "diagnostic_tool": spec.get("diagnostic_tool"),
        "diagnostic_body_built": diagnostic_body,
        "diagnostic_state": summarize_state(diagnostic_state),
        "bad_results": bad_results,
        "good_action": spec["good_action"],
        "good_body_built": bool(good_body_text),
        "good_judge": good_judge,
        "good_judge_accepted": None if good_judge is None else bool(good_judge.get("accepted")),
        "good_state": summarize_state(good_state),
        "lesson": spec.get("lesson"),
        "fewshot": fewshot,
        "capability_experiment": spec.get("capability_experiment"),
        "capability_modes": capability_modes,
        "seconds": round(time.monotonic() - started, 3),
    }


def build_fewshot(
    case_id: str,
    problem: dict[str, Any],
    spec: dict[str, Any],
    base_state: dict[str, Any],
    diagnostic_state: dict[str, Any] | None,
    bad_results: list[dict[str, Any]],
    good_body: bool,
    good_state: dict[str, Any] | None,
    good_judge: dict[str, Any] | None,
) -> dict[str, Any]:
    bad = bad_results[0] if bad_results else None
    feedback_source = summarize_state(diagnostic_state) if diagnostic_state else summarize_state(base_state)
    user_msg = {
        "problem_id": problem.get("id"),
        "H": problem.get("equation1"),
        "Goal": problem.get("equation2"),
        "mechanical_feedback": feedback_source,
    }
    repair_msg = {
        "kind": "midpoint_curriculum_example",
        "case_id": case_id,
        "family": spec.get("family"),
        "bad_guess": (bad or {}).get("action"),
        "bad_result": {
            "body_built": (bad or {}).get("body_built"),
            "state": (bad or {}).get("state"),
        } if bad else None,
        "repair_reasoning": spec.get("lesson"),
        "better_response": spec.get("good_action"),
        "better_response_mechanically_consumed": good_body,
        "better_response_judge_accepted": None if good_judge is None else bool(good_judge.get("accepted")),
        "better_state": summarize_state(good_state),
    }
    return {
        "prompt_user_message": user_msg,
        "assistant_response_with_reasoning": repair_msg,
        "compact_training_text": (
            f"Example {case_id}: feedback family={spec.get('family')}. "
            f"Bad guess {compact_json((bad or {}).get('action'), 500)} failed with "
            f"{compact_json((bad or {}).get('state'), 700)}. "
            f"Lesson: {spec.get('lesson')} "
            f"Return: {compact_json(spec.get('good_action'), 500)}"
        ),
    }


def select_live_train_rows(train_rows: list[dict[str, Any]], target_row: dict[str, Any], limit: int) -> list[dict[str, Any]]:
    """Prefer examples from the same feedback family, then fill with diversity."""
    if limit <= 0:
        return []
    same_family = [row for row in train_rows if row.get("family") == target_row.get("family")]
    other = [row for row in train_rows if row.get("family") != target_row.get("family")]
    selected: list[dict[str, Any]] = []
    seen: set[str] = set()
    for row in [*same_family, *other]:
        case_id = str(row.get("case_id"))
        if case_id in seen:
            continue
        seen.add(case_id)
        selected.append(row)
        if len(selected) >= limit:
            break
    return selected


def build_synthetic_alpha_target(source_row: dict[str, Any], args: argparse.Namespace) -> dict[str, Any]:
    mappings = {
        1: {"x": "p", "y": "q", "z": "r", "w": "s", "u": "t", "v": "k"},
        2: {"x": "m", "y": "n", "z": "o", "w": "l", "u": "j", "v": "k"},
    }
    mapping = mappings[args.live_alpha_variant]
    source_problem = problem_by_id(source_row["problem_id"])
    problem = {
        **source_problem,
        "id": f"synthetic_alpha_{source_problem['id']}",
        "equation1": alpha_rename_equation(source_problem["equation1"], mapping),
        "equation2": alpha_rename_equation(source_problem["equation2"], mapping),
        "synthetic_transform": {"kind": "alpha_rename", "mapping": mapping},
    }
    h_eq = solver.parse_equation(problem["equation1"])
    g_eq = solver.parse_equation(problem["equation2"])
    base_state = baseline_state(
        h_eq,
        g_eq,
        args.baseline_h_limit,
        args.baseline_lemma_limit,
        args.baseline_congruence_cap,
    )
    return {
        **source_row,
        "case_id": f"{source_row['case_id']}__alpha_holdout",
        "problem_id": problem["id"],
        "role": "synthetic_holdout",
        "h": problem["equation1"],
        "goal": problem["equation2"],
        "problem": problem,
        "baseline": summarize_state(base_state),
        "diagnostic_state": {},
        "synthetic_transform": problem["synthetic_transform"],
    }


def build_live_prompt(
    train_rows: list[dict[str, Any]],
    target_row: dict[str, Any],
    live_train_examples: int,
    *,
    capability_mask: Any = None,
    blind_target: bool = False,
    repair_history: list[dict[str, Any]] | None = None,
    blackboard_state: dict[str, Any] | None = None,
) -> str:
    examples = []
    selected_train = select_live_train_rows(train_rows, target_row, live_train_examples)
    for row in selected_train:
        examples.append(" ".join([
            f"H={row['h']}",
            f"Goal={row['goal']}.",
            row["fewshot"]["compact_training_text"],
        ]))
    target_feedback = target_row["diagnostic_state"] or target_row["baseline"]
    normalized_mask = solver.normalize_capability_mask(capability_mask)
    target_identity = [] if blind_target else [
        f"Problem id: {target_row['problem_id']}",
        f"Feedback family: {target_row['family']}",
    ]
    mask_directive = []
    if normalized_mask["disabled"]:
        mask_directive = [
            "Experimental capability intervention:",
            f"Withheld capabilities: {json.dumps(normalized_mask['disabled'])}",
            "These capabilities are genuinely unavailable. Do not request a withheld tool; reconstruct the missing step using available generic midpoint or lemma-chain primitives.",
        ]
    repair_directive = []
    if repair_history:
        repair_directive = [
            "Previous live attempts were mechanically checked and failed. Repair them; do not repeat an exact action:",
            compact_json(repair_history, 6000),
        ]
    blackboard_directive = []
    if blackboard_state is not None:
        blackboard_directive = [
            "Trusted monotone episode blackboard:",
            compact_json(blackboard_state, 6000),
            "The runner automatically retains trusted nodes. Propose only genuinely new missing nodes; never repeat a refuted node under different variable letters or reverse equality orientation.",
        ]
    return "\n\n".join([
        "You are System 2 in a trusted mechanical/LLM equational prover.",
        "Your job is to propose one untrusted midpoint or lemma_chain. The mechanical side will verify it.",
        "All displayed equations are universally quantified over their variables. Variable letters carry no meaning: alpha-renamed equations have exactly the same structure. Transfer helper shapes from a structurally matching example using any fresh variable names.",
        "Infer the algebraic family from the shape of H and Goal; the held-out family label may be hidden.",
        "Learn from these examples, especially bad guesses and repairs:",
        "\n".join(f"- {example}" for example in examples),
        "Now solve the held-out case.",
        *target_identity,
        f"H: {target_row['h']}",
        f"Goal: {target_row['goal']}",
        *mask_directive,
        "Mechanical feedback:",
        compact_json(target_feedback, 5000),
        *blackboard_directive,
        *repair_directive,
        "A small-model refutation is decisive: if its table satisfies H and violates a proposed midpoint, discard that midpoint and every alpha-equivalent repetition of it.",
        "Mechanical progress is monotone: when feedback says `proved_midpoints_not_consumed`, keep every equation in `proved_lemmas` and return one lemma_chain that contains them plus the missing structural helpers from the closest matching training example. Do not replace proved lemmas with an unrelated single midpoint.",
        "Projection repair rule: if feedback says `a ◇ b = a` or `a ◇ b = b` was proved but not consumed, return a lemma_chain with both proj_l and proj_r.",
        "Do not repeat the goal itself as a midpoint; propose reusable helper lemmas or a strictly simpler bridge.",
        "Return exactly one JSON object. Prefer midpoint or lemma_chain. No prose.",
    ])


def run_live_probe(rows: list[dict[str, Any]], args: argparse.Namespace) -> dict[str, Any] | None:
    train = [row for row in rows if row.get("role") == "train"]
    if args.live_target_case:
        targets = [row for row in rows if row.get("case_id") == args.live_target_case]
    else:
        targets = [row for row in rows if row.get("role") == "holdout"]
    if not train or not targets:
        return None
    target = targets[0]
    if args.live_alpha_rename:
        target = build_synthetic_alpha_target(target, args)
    selected_train = select_live_train_rows(train, target, args.live_train_examples)
    experiment = target.get("capability_experiment") if args.live_paired_capability_modes else None
    curriculum_mask = (experiment or {}).get("curriculum_mask")
    negative_mask = (experiment or {}).get("negative_control_mask")
    problem = target.get("problem") or problem_by_id(target["problem_id"])
    h_eq = solver.parse_equation(problem["equation1"])
    g_eq = solver.parse_equation(problem["equation2"])
    prompt = ""
    llm: dict[str, Any] = {}
    parsed = None
    normalized = None
    submitted_action = None
    adapter_state = None
    body_built = False
    judge = None
    state = None
    negative_body = None
    negative_state = None
    negative_judge = None
    full_body = None
    full_state = None
    full_judge = None
    withheld_body = None
    withheld_state = None
    if experiment:
        full_action = experiment["full_mechanical_action"]
        full_body, full_state = run_action_body(full_action, h_eq, g_eq)
        full_judge = judge_true_body(problem, full_body, args.judge_timeout) if args.verify_judge else None
        withheld_body, withheld_state = run_action_body(
            full_action,
            h_eq,
            g_eq,
            capability_mask=curriculum_mask,
        )
    repair_history: list[dict[str, Any]] = []
    live_attempts: list[dict[str, Any]] = []
    prompt_chars_total = 0
    llm_config = load_config(args.config)
    blackboard = LemmaBlackboard() if args.live_stateful_blackboard else None
    for round_index in range(max(1, args.live_rounds)):
        prompt = build_live_prompt(
            train,
            target,
            args.live_train_examples,
            capability_mask=curriculum_mask,
            blind_target=args.live_blind_target,
            repair_history=repair_history,
            blackboard_state=blackboard.snapshot() if blackboard is not None else None,
        )
        prompt_chars_total += len(prompt)
        llm = call_chat(prompt, llm_config, timeout=args.live_timeout)
        parsed = solver.extract_json(llm.get("response", "")) if not llm.get("error") else None
        normalized, adapter_state = solver.normalize_llm_action(parsed) if isinstance(parsed, dict) else (None, None)
        submitted_action = normalized
        blackboard_preflight = None
        blackboard_update = None
        body_text = None
        state = None
        judge = None
        if normalized is not None and blackboard is not None:
            submitted_action, blackboard_preflight = blackboard.materialize_action(
                normalized,
                round_index=round_index + 1,
            )
        if submitted_action is not None:
            body_text, state = run_action_body(
                submitted_action,
                h_eq,
                g_eq,
                capability_mask=curriculum_mask,
            )
            if blackboard is not None:
                blackboard_update = blackboard.absorb_mechanical_state(
                    submitted_action,
                    state,
                    round_index=round_index + 1,
                )
            if args.verify_judge and body_text:
                judge = judge_true_body(problem, body_text, args.judge_timeout)
        elif blackboard_preflight is not None:
            state = blackboard_preflight
        body_built = bool(body_text)
        accepted = body_built and (not args.verify_judge or bool((judge or {}).get("accepted")))
        attempt = {
            "round": round_index + 1,
            "prompt_chars": len(prompt),
            "prompt_sha256": sha256_text(prompt),
            "llm_error": llm.get("error"),
            "llm_text": short_text(llm.get("response"), 1600),
            "parsed": parsed,
            "normalized": normalized,
            "submitted_action": submitted_action,
            "adapter_state": adapter_state,
            "blackboard_preflight": blackboard_preflight,
            "blackboard_update": blackboard_update,
            "blackboard_after": blackboard.snapshot() if blackboard is not None else None,
            "body_built": body_built,
            "judge": judge,
            "accepted": accepted,
            "state": summarize_state(state),
        }
        live_attempts.append(attempt)
        if accepted:
            break
        repair_history.append({
            "round": round_index + 1,
            "action": normalized or parsed,
            "submitted_action": submitted_action,
            "adapter_state": adapter_state,
            "mechanical_state": summarize_state(state),
            "judge": judge,
        })
    if experiment and submitted_action is not None:
        negative_body, negative_state = run_action_body(
            submitted_action,
            h_eq,
            g_eq,
            capability_mask=negative_mask,
        )
        if args.verify_judge and negative_body:
            negative_judge = judge_true_body(problem, negative_body, args.judge_timeout)
    attribution = None
    if experiment:
        attribution = {
            "full_mechanical_baseline_succeeds": bool(full_body),
            "full_mechanical_judge_accepted": None if full_judge is None else bool(full_judge.get("accepted")),
            "shortcut_is_actually_withheld": not bool(withheld_body) and (withheld_state or {}).get("status") == "withheld_for_curriculum",
            "live_response_is_bridge_action": bool(normalized and solver.is_hint_payload(normalized)),
            "live_recovery_succeeds_under_withholding": body_built,
            "live_recovery_judge_accepted": None if judge is None else bool(judge.get("accepted")),
            "negative_control_removes_recovery": not bool(negative_body),
        }
        required = [
            attribution["full_mechanical_baseline_succeeds"],
            attribution["shortcut_is_actually_withheld"],
            attribution["live_response_is_bridge_action"],
            attribution["live_recovery_succeeds_under_withholding"],
            attribution["negative_control_removes_recovery"],
        ]
        if args.verify_judge:
            required.extend([
                attribution["full_mechanical_judge_accepted"],
                attribution["live_recovery_judge_accepted"],
            ])
        attribution["live_system2_reconstruction_passes"] = all(value is True for value in required)
    return {
        "target_case_id": target["case_id"],
        "target_problem_id": target["problem_id"],
        "selected_train_case_ids": [row["case_id"] for row in selected_train],
        "synthetic_transform": target.get("synthetic_transform"),
        "target_identity_blinded": args.live_blind_target,
        "curriculum_capability_mask": solver.normalize_capability_mask(curriculum_mask),
        "negative_control_mask": solver.normalize_capability_mask(negative_mask),
        "prompt_chars": len(prompt),
        "prompt_chars_total": prompt_chars_total,
        "live_rounds_requested": args.live_rounds,
        "live_attempts": live_attempts,
        "evaluation_contract": {
            "schema_version": 1,
            "split_label": args.live_split_label,
            "stateful_blackboard": blackboard is not None,
            "llm": public_llm_config(llm_config),
            "config_sha256": sha256_file(args.config),
            "code_sha256": {
                "baby_solver.py": sha256_file(ROOT / "baby_solver.py"),
                "curriculum_blackboard.py": sha256_file(ROOT / "curriculum_blackboard.py"),
                "midpoint_curriculum_probe.py": sha256_file(Path(__file__)),
            },
            "capability_manifest_sha256": sha256_text(
                json.dumps(solver.capability_manifest(curriculum_mask), sort_keys=True)
            ),
            "prompt_sha256": [attempt["prompt_sha256"] for attempt in live_attempts],
        },
        "llm_response": llm,
        "parsed": parsed,
        "normalized": normalized,
        "submitted_action": submitted_action,
        "adapter_state": adapter_state,
        "blackboard": blackboard.snapshot() if blackboard is not None else None,
        "body_built": body_built,
        "judge": judge,
        "judge_accepted": None if judge is None else bool(judge.get("accepted")),
        "state": summarize_state(state),
        "full_mechanical": {
            "body_built": bool(full_body),
            "judge": full_judge,
            "state": summarize_state(full_state),
        } if experiment else None,
        "withheld_shortcut_check": {
            "body_built": bool(withheld_body),
            "state": summarize_state(withheld_state),
        } if experiment else None,
        "negative_control": {
            "body_built": bool(negative_body),
            "judge": negative_judge,
            "state": summarize_state(negative_state),
        } if experiment else None,
        "attribution": attribution,
    }


def summarize_live_probe(live: dict[str, Any]) -> dict[str, Any]:
    llm_response = live.get("llm_response") if isinstance(live.get("llm_response"), dict) else {}
    return {
        "target_case_id": live.get("target_case_id"),
        "target_problem_id": live.get("target_problem_id"),
        "selected_train_case_ids": live.get("selected_train_case_ids"),
        "synthetic_transform": live.get("synthetic_transform"),
        "target_identity_blinded": live.get("target_identity_blinded"),
        "curriculum_capability_mask": live.get("curriculum_capability_mask"),
        "negative_control_mask": live.get("negative_control_mask"),
        "prompt_chars": live.get("prompt_chars"),
        "prompt_chars_total": live.get("prompt_chars_total"),
        "live_rounds_requested": live.get("live_rounds_requested"),
        "live_attempts": live.get("live_attempts"),
        "evaluation_contract": live.get("evaluation_contract"),
        "llm_error": llm_response.get("error"),
        "llm_text": short_text(llm_response.get("response"), 1200),
        "parsed": live.get("parsed"),
        "normalized": live.get("normalized"),
        "submitted_action": live.get("submitted_action"),
        "blackboard": live.get("blackboard"),
        "body_built": live.get("body_built"),
        "judge_accepted": live.get("judge_accepted"),
        "judge": live.get("judge"),
        "state": live.get("state"),
        "full_mechanical": live.get("full_mechanical"),
        "withheld_shortcut_check": live.get("withheld_shortcut_check"),
        "negative_control": live.get("negative_control"),
        "attribution": live.get("attribution"),
    }


def write_markdown(rows: list[dict[str, Any]], live: dict[str, Any] | None, path: Path) -> None:
    lines = [
        "# LLM Midpoint Curriculum",
        "",
        "This file is generated by `scripts/midpoint_curriculum_probe.py`.",
        "It collects artificial-frontier examples where known midpoints or lemma chains teach item 3: LLM reach extension.",
        "Full machine-readable state is written to the `.artifacts` JSON output; this markdown keeps only the prompt lessons.",
        "",
    ]
    for row in rows:
        bad_summaries = [
            {
                "body_built": item["body_built"],
                "judge_accepted": item.get("judge_accepted"),
                "action": item["action"],
                "status": item["state"].get("status"),
                "need_hint": item["state"].get("need_hint"),
            }
            for item in row["bad_results"]
        ]
        lines.extend([
            f"## {row['case_id']}",
            "",
            f"- Problem: `{row['problem_id']}`",
            f"- Family: `{row['family']}`",
            f"- H: `{row['h']}`",
            f"- Goal: `{row['goal']}`",
            f"- Known good consumed: `{row['good_body_built']}`",
            f"- Known good judge accepted: `{row.get('good_judge_accepted')}`",
            f"- Lesson: {row.get('lesson')}",
            "",
            "Bad Guess Summary:",
            "",
            "```json",
            json.dumps(bad_summaries, indent=2, ensure_ascii=False),
            "```",
            "",
            "Better Response:",
            "",
            "```json",
            json.dumps(row["good_action"], indent=2, ensure_ascii=False),
            "```",
            "",
            "Compact Few-Shot Text:",
            "",
            "```text",
            row["fewshot"]["compact_training_text"],
            "```",
            "",
        ])
        if row.get("capability_modes") is not None:
            lines.extend([
                "Capability Intervention:",
                "",
                "```json",
                json.dumps({
                    "experiment": row["capability_modes"]["experiment"],
                    "attribution": row["capability_modes"]["attribution"],
                    "interpretation_limit": row["capability_modes"]["interpretation_limit"],
                }, indent=2, ensure_ascii=False),
                "```",
                "",
            ])
    if live is not None:
        lines.extend([
            "## Live Probe",
            "",
            "```json",
            json.dumps(summarize_live_probe(live), indent=2, ensure_ascii=False),
            "```",
            "",
        ])
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", action="append", choices=sorted(CURRICULUM), help="Case id to run; can repeat")
    parser.add_argument("--family", action="append", help="Run all cases in a family")
    parser.add_argument("--discover-family", action="append", choices=["right_square_chain", "square_sandwich_chain"], help="Cheaply discover candidate held-outs for a family")
    parser.add_argument("--discover-max-rows", type=int, help="Optional cap on true rows scanned by discovery")
    parser.add_argument("--output", type=Path, default=ROOT / ".artifacts" / "midpoint_curriculum_probe.json")
    parser.add_argument("--markdown-output", type=Path, default=ROOT / "docs" / "llm_midpoint_curriculum.md")
    parser.add_argument("--config", type=Path, default=ROOT / ".artifacts" / "openrouter_fast_config.json")
    parser.add_argument("--live", action="store_true", help="Run one live held-out uptake probe")
    parser.add_argument("--live-target-case", choices=sorted(CURRICULUM), help="Curriculum case to use as the live target")
    parser.add_argument("--live-timeout", type=float, default=75.0)
    parser.add_argument("--live-train-examples", type=int, default=1)
    parser.add_argument("--live-rounds", type=int, default=1, help="Maximum mechanically repaired live attempts")
    parser.add_argument("--live-stateful-blackboard", action="store_true", help="Retain proved lemmas and block alpha-equivalent refutations in first-class episode state")
    parser.add_argument(
        "--live-split-label",
        choices=["development", "sealed_test", "postmortem"],
        default="development",
        help="Evaluation provenance label recorded in the live artifact",
    )
    parser.add_argument("--live-alpha-rename", action="store_true", help="Use a synthetic alpha-renamed target")
    parser.add_argument("--live-alpha-variant", type=int, choices=[1, 2], default=1, help="Synthetic alpha-renaming map (use a fresh variant after protocol tuning)")
    parser.add_argument("--live-blind-target", action="store_true", help="Hide target problem id and family label from the LLM")
    parser.add_argument(
        "--live-paired-capability-modes",
        action="store_true",
        help="Evaluate the live response under curriculum and negative-control masks",
    )
    parser.add_argument("--baseline-h-limit", type=int, default=8)
    parser.add_argument("--baseline-lemma-limit", type=int, default=16)
    parser.add_argument("--baseline-congruence-cap", type=int, default=0)
    parser.add_argument("--keep-raw-states", action="store_true")
    parser.add_argument(
        "--paired-capability-modes",
        action="store_true",
        help="Replay configured cases with full, shortcut-withheld, recovery, and negative-control masks",
    )
    parser.add_argument("--verify-judge", action="store_true", help="Verify built true proof bodies with the official judge")
    parser.add_argument("--judge-timeout", type=int, default=20, help="Lean timeout per curriculum judge check")
    args = parser.parse_args()

    if args.discover_family:
        discoveries = [discover_family_candidates(family, args.discover_max_rows) for family in args.discover_family]
        result = {
            "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "discoveries": discoveries,
        }
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")
        print(json.dumps({
            "output": str(args.output),
            "discoveries": [
                {
                    "family": item["family"],
                    "rows_scanned": item["rows_scanned"],
                    "shaped_count": item["shaped_count"],
                    "focused_hit_count": item["focused_hit_count"],
                    "new_focused_hits": [row["id"] for row in item["new_focused_hits"]],
                    "seconds": item["seconds"],
                }
                for item in discoveries
            ],
        }, ensure_ascii=False))
        return 0

    selected = set(args.case or [])
    if args.live_target_case:
        selected.add(args.live_target_case)
        if args.live and CURRICULUM[args.live_target_case].get("role") != "train":
            target_family = CURRICULUM[args.live_target_case].get("family")
            selected.update(
                case_id
                for case_id, spec in CURRICULUM.items()
                if spec.get("role") == "train" and spec.get("family") == target_family
            )
    if args.family:
        for family in args.family:
            selected.update(case_id for case_id, spec in CURRICULUM.items() if spec["family"] == family)
    if not selected:
        selected = {
            "opconst_train_hard1_0034",
            "opconst_holdout_hard1_0046",
        }

    rows = [run_case(case_id, CURRICULUM[case_id], args) for case_id in sorted(selected)]
    live = run_live_probe(rows, args) if args.live else None
    result = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "capability_manifest": solver.capability_manifest(),
        "cases": rows,
        "live_probe": live,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(rows, live, args.markdown_output)
    print(json.dumps({
        "output": str(args.output),
        "markdown_output": str(args.markdown_output),
        "cases": [
            {
                "case_id": row["case_id"],
                "good_body_built": row["good_body_built"],
                "good_judge_accepted": row.get("good_judge_accepted"),
                "bad_body_built": [item["body_built"] for item in row["bad_results"]],
                "bad_judge_accepted": [item.get("judge_accepted") for item in row["bad_results"]],
                "capability_attribution": (
                    row["capability_modes"]["attribution"]
                    if row.get("capability_modes") is not None
                    else None
                ),
            }
            for row in rows
        ],
        "live_body_built": None if live is None else live.get("body_built"),
        "live_judge_accepted": None if live is None else live.get("judge_accepted"),
        "live_normalized": None if live is None else live.get("normalized"),
        "live_attribution": None if live is None else live.get("attribution"),
    }, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
