#!/usr/bin/env python3
"""Replay an E unit-equation proof trace through the trusted Lean renderer.

E is used only as a research teacher. Every imported equation must be
reconstructed by baby_solver's proof-carrying mechanics, and the final stitched
body is checked by the official Lean verifier.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import difflib
import json
import re
import sys
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
OFFICIAL = ROOT / "official-stage2"
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(OFFICIAL))

import baby_solver  # noqa: E402
from research_system.curriculum import load_problem  # noqa: E402
from research_system.protocol import ExecutionResult, ProblemSpec  # noqa: E402
from research_system.verifier import OfficialLeanVerifier  # noqa: E402


@dataclass(frozen=True)
class TraceClause:
    clause_id: int
    equation: dict[str, Any]
    parents: tuple[int, ...]
    inference: str


def split_top_level_equation(formula: str) -> tuple[str, str]:
    depth = 0
    for index, char in enumerate(formula):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif char == "=" and depth == 0:
            return formula[:index], formula[index + 1 :]
    raise ValueError(f"not a positive unit equation: {formula}")


def parse_tptp_term(text: str) -> baby_solver.Term:
    text = text.strip()
    operation = next(
        (name for name in ("f", "op") if text.startswith(f"{name}(") and text.endswith(")")),
        None,
    )
    if operation is not None:
        inner = text[len(operation) + 1 : -1]
        depth = 0
        for index, char in enumerate(inner):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
            elif char == "," and depth == 0:
                return (
                    "op",
                    parse_tptp_term(inner[:index]),
                    parse_tptp_term(inner[index + 1 :]),
                )
        raise ValueError(f"binary f term has no top-level comma: {text}")
    if re.fullmatch(r"X\d+", text):
        return ("var", f"v{text[1:]}")
    raise ValueError(f"unsupported TPTP term: {text}")


def load_input_problem(problem_id: str, problem_file: Path | None) -> ProblemSpec:
    if problem_file is None:
        return load_problem(problem_id)
    text = problem_file.read_text(encoding="utf-8").strip()
    if not text:
        raise ValueError(f"empty problem file: {problem_file}")
    rows = json.loads(text) if text.startswith("[") else [
        json.loads(line) for line in text.splitlines() if line.strip()
    ]
    for row in rows:
        if isinstance(row, dict) and row.get("id") == problem_id:
            return ProblemSpec.from_mapping(row)
    raise KeyError(f"problem not found in {problem_file}: {problem_id}")


def balanced_chunk(text: str, start: int) -> tuple[str, int]:
    if text[start] != "(":
        raise ValueError("balanced chunk must start at an opening parenthesis")
    depth = 0
    for index in range(start, len(text)):
        char = text[index]
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0:
                return text[start + 1 : index], index + 1
    raise ValueError("unterminated parenthesized TPTP formula")


def parse_trace(path: Path) -> list[TraceClause]:
    clauses: list[TraceClause] = []
    prefix = re.compile(r"^cnf\(c_0_(\d+),\s*plain,\s*")
    for line in path.read_text(encoding="utf-8").splitlines():
        match = prefix.match(line)
        if match is None:
            continue
        clause_id = int(match.group(1))
        formula, end = balanced_chunk(line, match.end())
        if "!=" in formula:
            continue
        try:
            lhs_text, rhs_text = split_top_level_equation(formula)
            lhs = parse_tptp_term(lhs_text)
            rhs = parse_tptp_term(rhs_text)
        except ValueError:
            continue
        variables = baby_solver.pc_vars_of(lhs)
        variables += [
            var
            for var in baby_solver.pc_vars_of(rhs)
            if var not in variables
        ]
        tail = line[end:]
        parent_ids: list[int] = []
        for raw_parent in re.findall(r"c_0_(\d+)", tail):
            parent = int(raw_parent)
            if parent != clause_id and parent not in parent_ids:
                parent_ids.append(parent)
        inference_match = re.search(r"inference\(([^,\]]+)", tail)
        clauses.append(
            TraceClause(
                clause_id=clause_id,
                equation={
                    "text": (
                        f"{baby_solver.term_to_str(lhs)} = "
                        f"{baby_solver.term_to_str(rhs)}"
                    ),
                    "variables": variables,
                    "lhs": lhs,
                    "rhs": rhs,
                },
                parents=tuple(parent_ids),
                inference=(
                    inference_match.group(1)
                    if inference_match is not None
                    else "unknown"
                ),
            )
        )
    return clauses


def same_equation(left: dict[str, Any], right: dict[str, Any]) -> bool:
    return (
        baby_solver.pc_canon(left["lhs"], left["rhs"])
        == baby_solver.pc_canon(right["lhs"], right["rhs"])
    )


def focused_replay(
    target: TraceClause,
    available: dict[int, TraceClause],
    names: dict[int, str],
    *,
    rounds: int,
    time_budget: float,
) -> tuple[str | None, dict[str, Any]]:
    parent_ids = [
        parent
        for parent in target.parents
        if parent in available and parent in names
    ]
    if not parent_ids:
        return None, {
            "status": "no_available_parents",
            "requested_parents": list(target.parents),
        }
    start = [
        (available[parent].equation["lhs"], available[parent].equation["rhs"])
        for parent in parent_ids
    ]
    target_signature = baby_solver.pc_canon(
        target.equation["lhs"],
        target.equation["rhs"],
    )
    target_size = (
        baby_solver.term_size(target.equation["lhs"])
        + baby_solver.term_size(target.equation["rhs"])
    )
    target_id, records, metadata = baby_solver.pc_saturate(
        start,
        lambda pair: baby_solver.pc_canon(*pair) == target_signature,
        max_rounds=rounds,
        max_eqs=25_000,
        max_size=max(80, target_size * 3),
        time_budget=time_budget,
        allow_var_overlap=False,
    )
    state = {
        "status": "proved" if target_id is not None else "stuck",
        "parent_ids": parent_ids,
        "parent_names": [names[parent] for parent in parent_ids],
        "records_generated": len(records),
        "saturation": metadata,
    }
    if target_id is None:
        return None, state
    state["derivation_length"] = len(
        baby_solver.pc_derivation_chain(target_id, records)
    )
    return baby_solver.pc_render(
        target_id,
        records,
        target.equation["variables"],
        target.equation["lhs"],
        target.equation["rhs"],
        base_names=[names[parent] for parent in parent_ids],
    ), state


def linear_parent_replay(
    target: TraceClause,
    available: dict[int, TraceClause],
    names: dict[int, str],
    *,
    max_depth: int,
    beam_width: int,
    time_budget: float,
) -> tuple[str | None, dict[str, Any]]:
    """Follow E's first parent while repeatedly applying its other parents.

    E's `spm` and `rw` steps can rewrite several equal occurrences at once.
    baby_solver deliberately renders one congruence step at a time, so this
    bounded beam expands a single E edge into a short Lean-friendly chain.
    """
    parent_ids = [
        parent
        for parent in target.parents
        if parent in available and parent in names
    ]
    if len(parent_ids) < 2:
        return None, {
            "status": "insufficient_available_parents",
            "parent_ids": parent_ids,
        }

    records: list[dict[str, Any]] = []
    seen: dict[tuple[str, str], int] = {}
    for base_index, parent in enumerate(parent_ids):
        equation = available[parent].equation
        signature = tuple(
            map(
                baby_solver.term_key,
                baby_solver.pc_canon(equation["lhs"], equation["rhs"]),
            )
        )
        seen[signature] = len(records)
        records.append({
            "lhs": equation["lhs"],
            "rhs": equation["rhs"],
            "binders": equation["variables"],
            "deriv": None,
            "base": base_index,
        })

    target_signature = baby_solver.pc_canon(
        target.equation["lhs"],
        target.equation["rhs"],
    )
    target_text = (
        f"{baby_solver.term_to_str(target.equation['lhs'])}="
        f"{baby_solver.term_to_str(target.equation['rhs'])}"
    )
    target_size = (
        baby_solver.term_size(target.equation["lhs"])
        + baby_solver.term_size(target.equation["rhs"])
    )
    max_size = max(80, target_size * 3)
    frontier = [0]
    rule_ids = list(range(1, len(parent_ids)))
    counter = [0]
    deadline = time.monotonic() + time_budget
    depth_rows: list[dict[str, Any]] = []

    for depth in range(1, max_depth + 1):
        candidates: list[tuple[float, int]] = []
        for current_id in frontier:
            if time.monotonic() > deadline:
                return None, {
                    "status": "time_budget",
                    "parent_ids": parent_ids,
                    "records_generated": len(records),
                    "depths": depth_rows,
                }
            for rule_id in rule_ids:
                for left_id, right_id in (
                    (current_id, rule_id),
                    (rule_id, current_id),
                ):
                    outputs = baby_solver.pc_paramodulants(
                        records[left_id],
                        records[right_id],
                        counter,
                        max_size,
                        allow_var_overlap=False,
                    )
                    for (
                        lhs,
                        rhs,
                        binders,
                        args_left,
                        args_right,
                        proof_info,
                    ) in outputs:
                        canonical = baby_solver.pc_canon(lhs, rhs)
                        signature = tuple(map(baby_solver.term_key, canonical))
                        if signature in seen:
                            continue
                        record_id = len(records)
                        seen[signature] = record_id
                        records.append({
                            "lhs": lhs,
                            "rhs": rhs,
                            "binders": binders,
                            "deriv": (
                                left_id,
                                right_id,
                                args_left,
                                args_right,
                                proof_info,
                            ),
                            "base": None,
                        })
                        if canonical == target_signature:
                            return baby_solver.pc_render(
                                record_id,
                                records,
                                target.equation["variables"],
                                target.equation["lhs"],
                                target.equation["rhs"],
                                base_names=[names[parent] for parent in parent_ids],
                            ), {
                                "status": "proved",
                                "parent_ids": parent_ids,
                                "parent_names": [
                                    names[parent] for parent in parent_ids
                                ],
                                "records_generated": len(records),
                                "depth": depth,
                                "derivation_length": len(
                                    baby_solver.pc_derivation_chain(
                                        record_id,
                                        records,
                                    )
                                ),
                                "depths": depth_rows,
                            }
                        candidate_text = (
                            f"{baby_solver.term_to_str(lhs)}="
                            f"{baby_solver.term_to_str(rhs)}"
                        )
                        score = difflib.SequenceMatcher(
                            None,
                            candidate_text,
                            target_text,
                            autojunk=False,
                        ).ratio()
                        candidates.append((score, record_id))
        candidates.sort(reverse=True)
        frontier = [
            record_id
            for _score, record_id in candidates[:beam_width]
        ]
        depth_rows.append({
            "depth": depth,
            "candidates": len(candidates),
            "retained": len(frontier),
            "best_similarity": (
                round(candidates[0][0], 4)
                if candidates
                else None
            ),
        })
        if not frontier:
            break

    return None, {
        "status": "depth_exhausted",
        "parent_ids": parent_ids,
        "records_generated": len(records),
        "depths": depth_rows,
    }


def match_rewrite_pattern(
    pattern: baby_solver.Term,
    subject: baby_solver.Term,
    substitution: dict[str, baby_solver.Term],
) -> bool:
    if pattern[0] == "var":
        previous = substitution.get(pattern[1])
        if previous is None:
            substitution[pattern[1]] = subject
            return True
        return previous == subject
    return (
        subject[0] == "op"
        and match_rewrite_pattern(pattern[1], subject[1], substitution)
        and match_rewrite_pattern(pattern[2], subject[2], substitution)
    )


def apply_rewrite_substitution(
    term: baby_solver.Term,
    substitution: dict[str, baby_solver.Term],
) -> baby_solver.Term:
    if term[0] == "var":
        return substitution[term[1]]
    return (
        "op",
        apply_rewrite_substitution(term[1], substitution),
        apply_rewrite_substitution(term[2], substitution),
    )


def rewrite_once(
    term: baby_solver.Term,
    lhs: baby_solver.Term,
    rhs: baby_solver.Term,
) -> tuple[baby_solver.Term, bool]:
    if term[0] == "op":
        rewritten, changed = rewrite_once(term[1], lhs, rhs)
        if changed:
            return ("op", rewritten, term[2]), True
        rewritten, changed = rewrite_once(term[2], lhs, rhs)
        if changed:
            return ("op", term[1], rewritten), True
    substitution: dict[str, baby_solver.Term] = {}
    if match_rewrite_pattern(lhs, term, substitution):
        return apply_rewrite_substitution(rhs, substitution), True
    return term, False


def rewrite_once_detailed(
    term: baby_solver.Term,
    lhs: baby_solver.Term,
    rhs: baby_solver.Term,
    position: tuple[int, ...] = (),
) -> tuple[baby_solver.Term, dict[str, Any] | None]:
    if term[0] == "op":
        rewritten, details = rewrite_once_detailed(
            term[1],
            lhs,
            rhs,
            position + (0,),
        )
        if details is not None:
            return ("op", rewritten, term[2]), details
        rewritten, details = rewrite_once_detailed(
            term[2],
            lhs,
            rhs,
            position + (1,),
        )
        if details is not None:
            return ("op", term[1], rewritten), details
    substitution: dict[str, baby_solver.Term] = {}
    if match_rewrite_pattern(lhs, term, substitution):
        return apply_rewrite_substitution(rhs, substitution), {
            "position": position,
            "substitution": substitution,
        }
    return term, None


def explicit_rewrite_steps(
    term: baby_solver.Term,
    rules: list[tuple[int, dict[str, Any]]],
    *,
    limit: int = 64,
) -> tuple[baby_solver.Term, list[dict[str, Any]]]:
    steps: list[dict[str, Any]] = []
    while len(steps) < limit:
        changed = False
        for rule_id, equation in rules:
            before = term
            term, details = rewrite_once_detailed(
                term,
                equation["lhs"],
                equation["rhs"],
            )
            if details is None:
                continue
            steps.append({
                "rule_id": rule_id,
                "before": before,
                "after": term,
                **details,
            })
            changed = True
            break
        if not changed:
            break
    return term, steps


def rewrite_normal_form(
    term: baby_solver.Term,
    rules: list[tuple[baby_solver.Term, baby_solver.Term]],
    *,
    limit: int = 64,
) -> tuple[baby_solver.Term, int]:
    count = 0
    while count < limit:
        changed = False
        for lhs, rhs in rules:
            term, changed = rewrite_once(term, lhs, rhs)
            if changed:
                count += 1
                break
        if not changed:
            return term, count
    return term, count


def alpha_instance(
    pattern: baby_solver.Term,
    subject: baby_solver.Term,
    substitution: dict[str, baby_solver.Term],
) -> bool:
    if pattern[0] == "var":
        previous = substitution.get(pattern[1])
        if previous is None:
            substitution[pattern[1]] = subject
            return True
        return previous == subject
    return (
        subject[0] == "op"
        and alpha_instance(pattern[1], subject[1], substitution)
        and alpha_instance(pattern[2], subject[2], substitution)
    )


def instantiate_term(
    term: baby_solver.Term,
    substitution: dict[str, baby_solver.Term],
) -> baby_solver.Term:
    """Apply an alpha-instantiation simultaneously, without variable capture."""
    if term[0] == "var":
        return substitution.get(term[1], term)
    return (
        "op",
        instantiate_term(term[1], substitution),
        instantiate_term(term[2], substitution),
    )


def rewrite_normalization_replay(
    target: TraceClause,
    available: dict[int, TraceClause],
    names: dict[int, str],
) -> tuple[str | None, dict[str, Any]]:
    """Expand E's nested `spm` followed by one or more `rw` inferences."""
    parent_ids = [
        parent
        for parent in target.parents
        if parent in available and parent in names
    ]
    if target.inference != "rw" or len(parent_ids) < 2:
        return None, {
            "status": "not_a_supported_rw_edge",
            "parent_ids": parent_ids,
        }

    parent_records: list[dict[str, Any]] = []
    for base_index, parent in enumerate(parent_ids[:2]):
        equation = available[parent].equation
        parent_records.append({
            "lhs": equation["lhs"],
            "rhs": equation["rhs"],
            "binders": equation["variables"],
            "deriv": None,
            "base": base_index,
        })
    rule_ids = parent_ids[2:] if len(parent_ids) > 2 else parent_ids[1:]
    rules = [
        (
            available[parent].equation["lhs"],
            available[parent].equation["rhs"],
        )
        for parent in rule_ids
    ]
    target_lhs = target.equation["lhs"]
    target_rhs = target.equation["rhs"]
    counter = [0]
    candidates_checked = 0

    for left_id, right_id in ((0, 1), (1, 0)):
        for (
            lhs,
            rhs,
            binders,
            args_left,
            args_right,
            proof_info,
        ) in baby_solver.pc_paramodulants(
            parent_records[left_id],
            parent_records[right_id],
            counter,
            max(
                100,
                4
                * (
                    baby_solver.term_size(target_lhs)
                    + baby_solver.term_size(target_rhs)
                ),
            ),
            allow_var_overlap=False,
        ):
            candidates_checked += 1
            normalized_lhs, lhs_rewrites = rewrite_normal_form(lhs, rules)
            normalized_rhs, rhs_rewrites = rewrite_normal_form(rhs, rules)
            for expected_lhs, expected_rhs, symmetric in (
                (target_lhs, target_rhs, False),
                (target_rhs, target_lhs, True),
            ):
                substitution: dict[str, baby_solver.Term] = {}
                if not alpha_instance(
                    normalized_lhs,
                    expected_lhs,
                    substitution,
                ):
                    continue
                if not alpha_instance(
                    normalized_rhs,
                    expected_rhs,
                    substitution,
                ):
                    continue

                record = {
                    "lhs": lhs,
                    "rhs": rhs,
                    "binders": binders,
                    "deriv": (
                        left_id,
                        right_id,
                        args_left,
                        args_right,
                        proof_info,
                    ),
                    "base": None,
                }
                left_name = names[parent_ids[left_id]]
                right_name = names[parent_ids[right_id]]
                left_line = (
                    f"have ia := {left_name} "
                    + " ".join(baby_solver.pc_arg(arg) for arg in args_left)
                    if args_left
                    else f"have ia := {left_name}"
                )
                right_line = (
                    f"have ib := {right_name} "
                    + " ".join(baby_solver.pc_arg(arg) for arg in args_right)
                    if args_right
                    else f"have ib := {right_name}"
                )
                candidate_name = "trace_step"
                binder_chunk = " ".join(binders)
                lines = [
                    "intro " + " ".join(target.equation["variables"]),
                    (
                        f"have {candidate_name} : ∀ ({binder_chunk} : G), "
                        f"{baby_solver.term_to_str(lhs)} = "
                        f"{baby_solver.term_to_str(rhs)} := "
                        f"{baby_solver.pc_render_step_body(record, left_line, right_line)}"
                    ),
                ]
                default_arg = (
                    ("var", target.equation["variables"][0])
                    if target.equation["variables"]
                    else None
                )
                if default_arg is None and any(
                    binder not in substitution for binder in binders
                ):
                    continue
                if default_arg is not None:
                    for binder in binders:
                        substitution.setdefault(binder, default_arg)
                call_args = [
                    substitution[binder]
                    for binder in binders
                ]
                call = (
                    f"({candidate_name} "
                    + " ".join(
                        baby_solver.pc_arg(arg)
                        for arg in call_args
                        if arg is not None
                    )
                    + ")"
                )
                if symmetric:
                    call += ".symm"
                instantiated_lhs = instantiate_term(lhs, substitution)
                instantiated_rhs = instantiate_term(rhs, substitution)
                if symmetric:
                    instantiated_lhs, instantiated_rhs = (
                        instantiated_rhs,
                        instantiated_lhs,
                    )
                detailed_rules = [
                    (parent, available[parent].equation)
                    for parent in rule_ids
                ]
                final_lhs, left_steps = explicit_rewrite_steps(
                    instantiated_lhs,
                    detailed_rules,
                )
                final_rhs, right_steps = explicit_rewrite_steps(
                    instantiated_rhs,
                    detailed_rules,
                )
                if final_lhs != target_lhs or final_rhs != target_rhs:
                    continue
                current_name = "trace_eq0"
                lines.append(
                    f"have {current_name} : "
                    f"{baby_solver.term_to_str(instantiated_lhs)} = "
                    f"{baby_solver.term_to_str(instantiated_rhs)} := {call}"
                )
                current_lhs = instantiated_lhs
                current_rhs = instantiated_rhs
                step_index = 0
                for side, rewrite_steps in (
                    ("left", left_steps),
                    ("right", right_steps),
                ):
                    for rewrite in rewrite_steps:
                        step_index += 1
                        rule_id = int(rewrite["rule_id"])
                        rule_equation = available[rule_id].equation
                        rule_args = []
                        for variable in rule_equation["variables"]:
                            argument = rewrite["substitution"].get(
                                variable,
                                default_arg,
                            )
                            if argument is None:
                                break
                            rule_args.append(argument)
                        if len(rule_args) != len(rule_equation["variables"]):
                            break
                        rule_call = (
                            f"{names[rule_id]} "
                            + " ".join(
                                baby_solver.pc_arg(argument)
                                for argument in rule_args
                            )
                        ).rstrip()
                        before = rewrite["before"]
                        after = rewrite["after"]
                        context = baby_solver.pc_term_with_hole(
                            before,
                            tuple(rewrite["position"]),
                        )
                        lines.append(
                            f"have trace_rw{step_index} : "
                            f"{baby_solver.term_to_str(before)} = "
                            f"{baby_solver.term_to_str(after)} := "
                            f"congrArg (fun __pc_hole => {context}) "
                            f"({rule_call})"
                        )
                        next_name = f"trace_eq{step_index}"
                        if side == "left":
                            lines.append(
                                f"have {next_name} : "
                                f"{baby_solver.term_to_str(after)} = "
                                f"{baby_solver.term_to_str(current_rhs)} := "
                                f"trace_rw{step_index}.symm.trans {current_name}"
                            )
                            current_lhs = after
                        else:
                            lines.append(
                                f"have {next_name} : "
                                f"{baby_solver.term_to_str(current_lhs)} = "
                                f"{baby_solver.term_to_str(after)} := "
                                f"{current_name}.trans trace_rw{step_index}"
                            )
                            current_rhs = after
                        current_name = next_name
                lines.append(f"exact {current_name}")
                return "\n".join(lines), {
                    "status": "proved",
                    "parent_ids": parent_ids,
                    "rule_ids": rule_ids,
                    "candidates_checked": candidates_checked,
                    "rewrites": len(left_steps) + len(right_steps),
                    "symmetric": symmetric,
                }

    return None, {
        "status": "no_normalizing_candidate",
        "parent_ids": parent_ids,
        "rule_ids": rule_ids,
        "candidates_checked": candidates_checked,
    }


def compact_state(state: dict[str, Any]) -> dict[str, Any]:
    return baby_solver.compact_feedback_value(state, string_limit=300)


def run(args: argparse.Namespace) -> dict[str, Any]:
    problem = load_input_problem(args.problem_id, args.problem_file)
    h_eq = baby_solver.parse_equation(problem.equation1)
    g_eq = baby_solver.parse_equation(problem.equation2)
    trace = parse_trace(args.trace)
    trace_by_id = {clause.clause_id: clause for clause in trace}
    names: dict[int, str] = {}
    assumptions: list[baby_solver.UniversalEquation] = []
    declarations: list[str] = []
    attempts: list[dict[str, Any]] = []
    started = time.monotonic()

    for clause in trace:
        if same_equation(clause.equation, h_eq):
            names[clause.clause_id] = "h"
            attempts.append({
                "clause_id": clause.clause_id,
                "status": "hypothesis",
                "equation": clause.equation["text"],
            })
            continue
        if same_equation(clause.equation, g_eq):
            # Keep the target out of the helper context. The final leg must
            # consume earlier certified lemmas rather than assume the answer.
            attempts.append({
                "clause_id": clause.clause_id,
                "status": "deferred_goal",
                "equation": clause.equation["text"],
            })
            continue

        attempt_started = time.monotonic()
        body, state = focused_replay(
            clause,
            trace_by_id,
            names,
            rounds=args.focused_rounds,
            time_budget=args.focused_budget,
        )
        route = "focused_parent_saturation"
        if body is None:
            focused_state = state
            body, state = rewrite_normalization_replay(
                clause,
                trace_by_id,
                names,
            )
            state = {
                "focused": compact_state(focused_state),
                "rewrite_normalization": state,
            }
            route = "rewrite_normalization_replay"
        if body is None:
            normalization_state = state
            body, state = linear_parent_replay(
                clause,
                trace_by_id,
                names,
                max_depth=args.linear_depth,
                beam_width=args.linear_beam,
                time_budget=args.linear_budget,
            )
            state = {
                "normalization": compact_state(normalization_state),
                "linear": state,
            }
            route = "linear_parent_replay"
        if body is None:
            replay_state = state
            body, fallback_state = baby_solver.prove_with_assumptions_detailed(
                h_eq,
                clause.equation,
                assumptions,
                superposition_budget=args.fallback_budget,
            )
            state = {
                "replay": compact_state(replay_state),
                "fallback": compact_state(fallback_state),
            }
            route = "existing_consumer"

        elapsed = time.monotonic() - attempt_started
        attempt = {
            "clause_id": clause.clause_id,
            "equation": clause.equation["text"],
            "parents": list(clause.parents),
            "inference": clause.inference,
            "status": "proved" if body is not None else "stuck",
            "route": route,
            "seconds": round(elapsed, 6),
            "state": compact_state(state),
        }
        attempts.append(attempt)
        print(
            f"c_0_{clause.clause_id}: {attempt['status']} via {route} "
            f"({elapsed:.3f}s)",
            flush=True,
        )
        if body is None:
            return {
                "problem_id": problem.id,
                "trace": str(args.trace),
                "status": "trace_replay_stuck",
                "stuck_clause": clause.clause_id,
                "attempts": attempts,
                "elapsed_seconds": round(time.monotonic() - started, 6),
            }

        name = f"e{clause.clause_id}"
        names[clause.clause_id] = name
        assumptions.append(
            baby_solver.UniversalEquation(
                name=name,
                eq=clause.equation,
                extra_args=[],
            )
        )
        declarations.extend([
            f"have {name} : {baby_solver.lemma_statement(clause.equation)} := by",
            baby_solver.indent(body, 2),
        ])

    target_body, target_state = baby_solver.prove_with_assumptions_detailed(
        h_eq,
        g_eq,
        assumptions,
        superposition_budget=args.target_budget,
    )
    if target_body is None:
        return {
            "problem_id": problem.id,
            "trace": str(args.trace),
            "status": "target_leg_stuck",
            "attempts": attempts,
            "target_state": compact_state(target_state),
            "elapsed_seconds": round(time.monotonic() - started, 6),
        }

    final_body = "\n".join([*declarations, target_body])
    verifier = OfficialLeanVerifier(timeout_seconds=args.lean_timeout)
    verification = verifier.verify(
        problem,
        ExecutionResult(status="candidate_ready", body=final_body),
    )
    if args.body_output:
        args.body_output.parent.mkdir(parents=True, exist_ok=True)
        args.body_output.write_text(final_body + "\n", encoding="utf-8")
    if args.certificate_output:
        args.certificate_output.parent.mkdir(parents=True, exist_ok=True)
        args.certificate_output.write_text(
            baby_solver.make_true_code(final_body),
            encoding="utf-8",
        )
    return {
        "problem_id": problem.id,
        "trace": str(args.trace),
        "status": "accepted" if verification.accepted else "lean_rejected",
        "helpers_proved": len(assumptions),
        "attempts": attempts,
        "target_state": compact_state(target_state),
        "verification": verification.to_mapping(),
        "body_output": str(args.body_output) if args.body_output else None,
        "certificate_output": (
            str(args.certificate_output) if args.certificate_output else None
        ),
        "elapsed_seconds": round(time.monotonic() - started, 6),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("problem_id")
    parser.add_argument("trace", type=Path)
    parser.add_argument("--problem-file", type=Path)
    parser.add_argument("--focused-rounds", type=int, default=3)
    parser.add_argument("--focused-budget", type=float, default=8.0)
    parser.add_argument("--linear-depth", type=int, default=5)
    parser.add_argument("--linear-beam", type=int, default=60)
    parser.add_argument("--linear-budget", type=float, default=10.0)
    parser.add_argument("--fallback-budget", type=float, default=8.0)
    parser.add_argument("--target-budget", type=float, default=12.0)
    parser.add_argument("--lean-timeout", type=int, default=45)
    parser.add_argument("--body-output", type=Path)
    parser.add_argument("--certificate-output", type=Path)
    parser.add_argument("--report-output", type=Path)
    args = parser.parse_args()
    report = run(args)
    rendered = json.dumps(report, indent=2, ensure_ascii=False)
    print(rendered)
    if args.report_output:
        args.report_output.parent.mkdir(parents=True, exist_ok=True)
        args.report_output.write_text(rendered + "\n", encoding="utf-8")
    raise SystemExit(0 if report.get("status") == "accepted" else 1)


if __name__ == "__main__":
    main()
