"""Structural fingerprints for equational problems and verified proof plans."""

from __future__ import annotations

from typing import Any

import baby_solver


STRUCTURE_VERSION = "sair-equation-structure-v1"


def _canonical_term(
    term: tuple,
    variables: dict[str, str],
    *,
    dual: bool = False,
    erase_variables: bool = False,
) -> str:
    if term[0] == "var":
        if erase_variables:
            return "v"
        raw = str(term[1])
        if raw not in variables:
            variables[raw] = f"v{len(variables)}"
        return variables[raw]
    left, right = term[1], term[2]
    if dual:
        left, right = right, left
    return (
        f"({_canonical_term(left, variables, dual=dual, erase_variables=erase_variables)}◇"
        f"{_canonical_term(right, variables, dual=dual, erase_variables=erase_variables)})"
    )


def canonical_equation_signature(
    equation: str,
    *,
    dual: bool = False,
    erase_variables: bool = False,
) -> str:
    """Canonicalize alpha-renaming, equality orientation, and optionally magma duality."""
    parsed = baby_solver.parse_equation(baby_solver.clean_equation_hint_text(equation))

    def oriented(left: tuple, right: tuple) -> str:
        variables: dict[str, str] = {}
        lhs = _canonical_term(left, variables, dual=dual, erase_variables=erase_variables)
        rhs = _canonical_term(right, variables, dual=dual, erase_variables=erase_variables)
        return f"{lhs}={rhs}"

    return min(
        oriented(parsed["lhs"], parsed["rhs"]),
        oriented(parsed["rhs"], parsed["lhs"]),
    )


def _dual_term(term: tuple) -> tuple:
    if term[0] == "var":
        return term
    return ("op", _dual_term(term[2]), _dual_term(term[1]))


def dual_equation(equation: str) -> str:
    """Render the opposite-magma image of a universal equation."""
    parsed = baby_solver.parse_equation(baby_solver.clean_equation_hint_text(equation))
    return (
        f"{baby_solver.term_to_str(_dual_term(parsed['lhs']))} = "
        f"{baby_solver.term_to_str(_dual_term(parsed['rhs']))}"
    )


def _term_metrics(term: tuple) -> tuple[int, int, list[str]]:
    if term[0] == "var":
        return 0, 0, [str(term[1])]
    left_depth, left_ops, left_vars = _term_metrics(term[1])
    right_depth, right_ops, right_vars = _term_metrics(term[2])
    return 1 + max(left_depth, right_depth), 1 + left_ops + right_ops, left_vars + right_vars


def equation_profile(equation: str) -> dict[str, Any]:
    parsed = baby_solver.parse_equation(baby_solver.clean_equation_hint_text(equation))
    signatures = {
        "canonical": canonical_equation_signature(equation),
        "dual": canonical_equation_signature(equation, dual=True),
        "coarse": canonical_equation_signature(equation, erase_variables=True),
        "coarse_dual": canonical_equation_signature(equation, dual=True, erase_variables=True),
    }
    signatures["duality_key"] = min(signatures["canonical"], signatures["dual"])
    signatures["coarse_duality_key"] = min(signatures["coarse"], signatures["coarse_dual"])
    side_metrics = [_term_metrics(parsed["lhs"]), _term_metrics(parsed["rhs"])]
    depths = sorted(metric[0] for metric in side_metrics)
    op_counts = sorted(metric[1] for metric in side_metrics)
    occurrences = [name for metric in side_metrics for name in metric[2]]
    multiplicities = sorted(
        (occurrences.count(name) for name in set(occurrences)),
        reverse=True,
    )
    features = {
        f"depths:{','.join(map(str, depths))}",
        f"ops:{','.join(map(str, op_counts))}",
        f"variables:{len(set(occurrences))}",
        f"occurrences:{len(occurrences)}",
        f"multiplicity:{','.join(map(str, multiplicities))}",
        f"roots:{','.join(sorted(term[0] for term in (parsed['lhs'], parsed['rhs'])))}",
        f"coarse:{signatures['coarse_duality_key']}",
    }
    return {
        "structure_version": STRUCTURE_VERSION,
        **signatures,
        "depths": depths,
        "op_counts": op_counts,
        "variable_count": len(set(occurrences)),
        "occurrence_count": len(occurrences),
        "multiplicities": multiplicities,
        "features": sorted(features),
    }


def problem_structure(problem: Any) -> dict[str, Any]:
    data = problem.to_mapping() if hasattr(problem, "to_mapping") else problem
    if not isinstance(data, dict):
        raise TypeError("problem structure requires a mapping or ProblemSpec")
    hypothesis = equation_profile(str(data["equation1"]))
    goal = equation_profile(str(data["equation2"]))
    pair = f"{hypothesis['canonical']}=>{goal['canonical']}"
    dual_pair = f"{hypothesis['dual']}=>{goal['dual']}"
    features = {
        *[f"h:{item}" for item in hypothesis["features"]],
        *[f"g:{item}" for item in goal["features"]],
        f"delta_ops:{sum(goal['op_counts']) - sum(hypothesis['op_counts'])}",
        f"delta_depth:{max(goal['depths']) - max(hypothesis['depths'])}",
    }
    return {
        "structure_version": STRUCTURE_VERSION,
        "pair_signature": pair,
        "dual_pair_signature": dual_pair,
        "pair_duality_key": min(pair, dual_pair),
        "hypothesis": hypothesis,
        "goal": goal,
        "features": sorted(features),
    }


def _jaccard(left: set[str], right: set[str]) -> float:
    union = left | right
    return len(left & right) / len(union) if union else 1.0


def structural_similarity(query: dict[str, Any], candidate: dict[str, Any]) -> tuple[float, list[str]]:
    """Transparent compatibility score; callers choose the acceptance threshold."""
    if query.get("structure_version") != STRUCTURE_VERSION:
        return 0.0, ["query_structure_version_mismatch"]
    if candidate.get("structure_version") != STRUCTURE_VERSION:
        return 0.0, ["candidate_structure_version_mismatch"]
    reasons: list[str] = []
    score = 0.0
    if query.get("pair_signature") == candidate.get("pair_signature"):
        score = 100.0
        reasons.append("exact_alpha_and_orientation_invariant_pair")
    elif query.get("pair_duality_key") == candidate.get("pair_duality_key"):
        score = 92.0
        reasons.append("magma_dual_pair")
    else:
        qh, ch = query.get("hypothesis") or {}, candidate.get("hypothesis") or {}
        qg, cg = query.get("goal") or {}, candidate.get("goal") or {}
        if qh.get("canonical") == ch.get("canonical"):
            score += 34.0
            reasons.append("same_hypothesis_shape")
        elif qh.get("duality_key") == ch.get("duality_key"):
            score += 29.0
            reasons.append("dual_hypothesis_shape")
        elif qh.get("coarse_duality_key") == ch.get("coarse_duality_key"):
            score += 12.0
            reasons.append("coarse_hypothesis_shape")
        if qg.get("canonical") == cg.get("canonical"):
            score += 30.0
            reasons.append("same_goal_shape")
        elif qg.get("duality_key") == cg.get("duality_key"):
            score += 25.0
            reasons.append("dual_goal_shape")
        elif qg.get("coarse_duality_key") == cg.get("coarse_duality_key"):
            score += 10.0
            reasons.append("coarse_goal_shape")
        feature_overlap = _jaccard(set(query.get("features") or []), set(candidate.get("features") or []))
        score += 20.0 * feature_overlap
        if feature_overlap:
            reasons.append(f"feature_jaccard:{feature_overlap:.3f}")
    return round(score, 6), reasons


def plan_node_signatures(artifact: dict[str, Any]) -> list[str]:
    payload = artifact.get("payload") if isinstance(artifact.get("payload"), dict) else {}
    nodes = payload.get("plan_nodes") if isinstance(payload.get("plan_nodes"), list) else []
    signatures = [
        str(node.get("signature"))
        for node in nodes
        if isinstance(node, dict) and node.get("signature")
    ]
    if signatures:
        return signatures
    action = payload.get("action_template") if isinstance(payload.get("action_template"), dict) else payload
    out = []
    for item in action.get("lemmas") or []:
        equation = item.get("equation") if isinstance(item, dict) else item
        if isinstance(equation, str):
            out.append(canonical_equation_signature(equation))
    return out


__all__ = [
    "STRUCTURE_VERSION",
    "canonical_equation_signature",
    "dual_equation",
    "equation_profile",
    "plan_node_signatures",
    "problem_structure",
    "structural_similarity",
]
