#!/usr/bin/env python3
"""Probe whether an LLM can use one mechanical feedback state.

This is intentionally not a coverage benchmark. It bypasses the full solver
scheduler, builds one protocol-v0 false-search miss, asks the LLM for the next
action, and records whether the response follows the feedback.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import baby_solver as solver  # noqa: E402


def load_first_problem(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line:
                return json.loads(line)
    raise ValueError(f"{path}: no JSONL rows found")


def load_config(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def call_chat(prompt: str, config: dict[str, Any], timeout: float) -> dict[str, Any]:
    llm = config.get("llm") or {}
    base_url = (llm.get("base_url") or os.environ.get("OPENAI_BASE_URL") or "https://openrouter.ai/api/v1").rstrip("/")
    api_key_env = llm.get("api_key_env")
    if api_key_env:
        api_key = os.environ.get(api_key_env, "")
    elif "openrouter.ai" in base_url:
        api_key = os.environ.get("OPENROUTER_API_KEY") or os.environ.get("OPENAI_API_KEY") or ""
    else:
        api_key = os.environ.get("OPENAI_API_KEY") or os.environ.get("OPENROUTER_API_KEY") or ""
    if not api_key:
        return {"error": f"{api_key_env or 'OPENAI_API_KEY/OPENROUTER_API_KEY'} not set"}

    body: dict[str, Any] = {
        "model": llm.get("model", "openai/gpt-oss-120b"),
        "messages": [
            {
                "role": "system",
                "content": "Return exactly one JSON object. No prose, markdown, or chain-of-thought.",
            },
            {"role": "user", "content": prompt},
        ],
        "temperature": float(llm.get("temperature", 0.0)),
        "max_tokens": int(llm.get("max_output_tokens", 1024)),
    }
    if "openrouter.ai" in base_url and llm.get("provider"):
        body["provider"] = {"order": [llm["provider"]]}
    if "openrouter.ai" in base_url and llm.get("reasoning_effort"):
        body["reasoning"] = {"effort": llm["reasoning_effort"]}

    request = urllib.request.Request(
        f"{base_url}/chat/completions",
        data=json.dumps(body).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=max(1.0, timeout)) as resp:
            payload = json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        return {"error": f"HTTP {exc.code}: {exc.read().decode('utf-8', 'replace')[:1000]}"}
    except Exception as exc:
        return {"error": repr(exc)}

    try:
        text = payload["choices"][0]["message"]["content"]
    except Exception:
        text = json.dumps(payload, ensure_ascii=False)
    return {"response": text, "raw": payload}


def classify_response(action: dict[str, Any] | None, state: dict[str, Any]) -> dict[str, Any]:
    recommended = state.get("recommended_next_call") or {}
    recommended_routes = [str(route) for route in recommended.get("routes") or []]
    highlights = state.get("diagnostic_highlights") or {}
    tried_routes = {
        str(route)
        for key in ("tried_routes", "tried_in_collaboration")
        for route in highlights.get(key) or []
    }
    if not action:
        return {
            "has_recommendation": bool(recommended_routes),
            "followed_recommendation": False,
            "repeated_tried_route": False,
            "supported_action": False,
            "selected_untried_route": False,
            "respected_no_recommendation": False,
            "kind": None,
        }
    routes = [str(route) for route in action.get("routes") or []]
    repeated = any(route in tried_routes for route in routes)
    selected_untried = bool(routes) and not repeated
    kind = str(action.get("kind") or "")
    raw_tool = str(action.get("tool") or "").strip()
    tool = solver.TOOL_ALIASES.get(raw_tool, raw_tool)
    supported = (
        kind in {"midpoint", "midpoint_chain", "lemma_hint", "lemma_chain", "false_table", "goal_proof"}
        or (kind == "tool_call" and tool in solver.TOOL_REGISTRY)
    )
    return {
        "kind": action.get("kind"),
        "tool": action.get("tool"),
        "routes": routes,
        "recommended_routes": recommended_routes,
        "has_recommendation": bool(recommended_routes),
        "followed_recommendation": bool(
            recommended_routes and routes and routes[: len(recommended_routes)] == recommended_routes
        ),
        "repeated_tried_route": repeated,
        "supported_action": supported,
        "selected_untried_route": selected_untried,
        "respected_no_recommendation": bool(not recommended_routes and not repeated and supported),
        "used_false_model_search": action.get("tool") == "false_model_search",
    }


def build_prompt(problem: dict[str, Any], false_state: dict[str, Any]) -> str:
    compact_state = {
        key: false_state.get(key)
        for key in (
            "protocol_version",
            "kind",
            "status",
            "source",
            "diagnostic_highlights",
            "untried_requested_routes",
            "recommended_next_call",
            "need_hint",
        )
    }
    return "\n".join([
        "You are System 2 in a trusted mechanical/LLM solver.",
        "The mechanical side is trusted; your output is only a hint/tool request.",
        f"Problem id: {problem.get('id')}",
        f"H: {problem.get('equation1')}",
        f"Goal: {problem.get('equation2')}",
        "Mechanical false-search feedback:",
        json.dumps(compact_state, ensure_ascii=False, indent=2),
        "Return one JSON action. Prefer recommended_next_call if it is present and not stale.",
        "Do not repeat routes listed under diagnostic_highlights.tried_routes or diagnostic_highlights.tried_in_collaboration.",
        "If recommended_next_call is null, return a genuinely new false route, a complete counterexample table, or a true-side midpoint/lemma_chain.",
        'There is no tool named "true_midpoint"; for a true-side bridge use {"kind":"midpoint","lemma":"<equation>"} or {"kind":"tool_call","tool":"lemma_chain","lemmas":[...]}.',
        "Allowed false action shape:",
        '{"kind":"tool_call","tool":"false_model_search","target":"goal","routes":["local_search:n=6:seed=0"],"budget":6}',
        "If false search looks exhausted, return a true-side midpoint or lemma_chain instead.",
    ])


def apply_memory_scenario(false_state: dict[str, Any], mode: str, budget: float) -> tuple[dict[str, Any], list[str]]:
    if mode == "none":
        return false_state, []
    if mode == "stale_first":
        recommended = false_state.get("recommended_next_call") or {}
        seeded = [str(route) for route in recommended.get("routes") or []]
        return solver.apply_false_route_memory(false_state, set(seeded), budget), seeded
    if mode == "exhaust_continuations":
        seeded = [str(route) for route in false_state.get("untried_requested_routes") or []]
        return solver.apply_false_route_memory(false_state, set(seeded), budget), seeded
    raise ValueError(f"unknown memory scenario: {mode}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--problem-file", type=Path, default=ROOT / ".artifacts" / "hard2_0125_only.jsonl")
    parser.add_argument("--config", type=Path, default=ROOT / ".artifacts" / "openrouter_fast_config.json")
    parser.add_argument("--routes", nargs="+", default=["model_finder_v2:n=5"])
    parser.add_argument("--budget", type=float, default=1.0)
    parser.add_argument(
        "--memory-scenario",
        choices=["none", "stale_first", "exhaust_continuations"],
        default="none",
        help="Mutate the mechanical feedback as if previous collaboration rounds had already tried some continuations.",
    )
    parser.add_argument("--timeout", type=float, default=75.0)
    parser.add_argument("--output", type=Path, default=ROOT / ".artifacts" / "feedback_uptake_probe.json")
    args = parser.parse_args()

    problem = load_first_problem(args.problem_file)
    h_eq = solver.parse_equation(problem["equation1"])
    g_eq = solver.parse_equation(problem["equation2"])
    started = time.monotonic()
    found, false_state = solver.false_model_search_detailed(
        h_eq,
        g_eq,
        {"routes": args.routes, "budget": args.budget},
        args.budget,
    )
    false_state, memory_seed_routes = apply_memory_scenario(false_state, args.memory_scenario, args.budget)
    prompt = build_prompt(problem, false_state)
    llm = call_chat(prompt, load_config(args.config), timeout=args.timeout)
    parsed = solver.extract_json(llm.get("response", "")) if not llm.get("error") else None
    normalized, adapter_state = solver.normalize_llm_action(parsed) if isinstance(parsed, dict) else (None, None)
    result = {
        "problem_id": problem.get("id"),
        "routes": args.routes,
        "memory_scenario": args.memory_scenario,
        "memory_seed_routes": memory_seed_routes,
        "mechanical_found": bool(found),
        "false_state": false_state,
        "prompt_chars": len(prompt),
        "llm_response": llm,
        "parsed": parsed,
        "normalized": normalized,
        "adapter_state": adapter_state,
        "uptake": classify_response(normalized, false_state),
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")
    print(json.dumps({
        "output": str(args.output),
        "uptake": result["uptake"],
        "adapter_status": (adapter_state or {}).get("status"),
        "error": llm.get("error"),
    }, ensure_ascii=False))
    return 0 if not llm.get("error") else 2


if __name__ == "__main__":
    raise SystemExit(main())
