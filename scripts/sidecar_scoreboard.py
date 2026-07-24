#!/usr/bin/env python3
"""Summarize llm_lean_sidecar JSONL transcripts.

This is intentionally lightweight: it treats transcripts as evidence logs and
extracts enough structure to compare tool behavior across flywheel runs.
"""

from __future__ import annotations

import argparse
import glob
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]


def _as_dict(value: Any) -> dict[str, Any]:
    return value if isinstance(value, dict) else {}


def _short(value: Any, *, limit: int = 120) -> str:
    text = "" if value is None else str(value)
    text = text.replace("\n", " ").strip()
    return text if len(text) <= limit else text[: limit - 1] + "..."


def _iter_jsonl(path: Path) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    try:
        with path.open("r", encoding="utf-8") as handle:
            for line_no, line in enumerate(handle, start=1):
                stripped = line.strip()
                if not stripped:
                    continue
                try:
                    item = json.loads(stripped)
                except json.JSONDecodeError:
                    events.append({
                        "type": "parse_error",
                        "line": line_no,
                        "error": "json_decode_error",
                    })
                    continue
                if isinstance(item, dict):
                    events.append(item)
    except OSError as exc:
        events.append({"type": "read_error", "error": str(exc)})
    return events


def _find_need_hints(value: Any, out: list[dict[str, Any]]) -> None:
    if isinstance(value, dict):
        hint = value.get("need_hint")
        if isinstance(hint, dict):
            out.append(hint)
        for nested in value.values():
            _find_need_hints(nested, out)
    elif isinstance(value, list):
        for nested in value:
            _find_need_hints(nested, out)


def _attempt_tool(attempt: dict[str, Any]) -> str:
    tool_call = _as_dict(attempt.get("tool_call"))
    module_state = _as_dict(attempt.get("module_state"))
    if tool_call.get("tool"):
        return str(tool_call["tool"])
    if module_state.get("tool"):
        return str(module_state["tool"])
    if attempt.get("false_model_hint"):
        return "false_model_hint"
    if attempt.get("lemma_hint"):
        return "lemma_hint"
    if attempt.get("lemma_chain"):
        return "lemma_chain"
    payload = _as_dict(attempt.get("llm_payload"))
    if payload.get("kind"):
        return str(payload["kind"])
    return "unknown"


def _attempt_status(attempt: dict[str, Any]) -> str:
    result = _as_dict(attempt.get("result"))
    return str(attempt.get("status") or result.get("status") or "unknown")


def _attempt_error(attempt: dict[str, Any]) -> str:
    result = _as_dict(attempt.get("result"))
    return str(attempt.get("error_code") or result.get("error_code") or "")


def summarize_transcript(path: Path) -> dict[str, Any]:
    events = _iter_jsonl(path)
    start = next((_as_dict(event) for event in events if event.get("type") == "start"), {})
    attempts = [_as_dict(event) for event in events if event.get("type") == "attempt"]
    routers = [_as_dict(event) for event in events if event.get("type") == "tool_router"]
    prompts = [_as_dict(event) for event in events if event.get("type") == "prompt"]

    tools: list[str] = []
    errors: list[str] = []
    accepted = False
    accepted_tool = ""
    counterexample_size = None
    false_model_source = ""
    need_hints: list[dict[str, Any]] = []
    statuses: list[str] = []

    for attempt in attempts:
        tool = _attempt_tool(attempt)
        status = _attempt_status(attempt)
        error = _attempt_error(attempt)
        tools.append(tool)
        statuses.append(status)
        if error:
            errors.append(error)
        _find_need_hints(attempt.get("module_state"), need_hints)
        _find_need_hints(attempt.get("result"), need_hints)
        result = _as_dict(attempt.get("result"))
        if status == "accepted":
            accepted = True
            accepted_tool = tool
            counterexample_size = result.get("counterexample_size")
            false_model_source = str(result.get("false_model_source") or "")

    problem_id = str(start.get("problem_id") or "")
    if not problem_id:
        for attempt in attempts:
            result = _as_dict(attempt.get("result"))
            problem_id = str(result.get("problem_id") or "")
            if problem_id:
                break
    if not problem_id:
        problem_id = path.stem

    signal = "accepted" if accepted else "stuck"
    if not attempts and any(event.get("type") == "parse_error" for event in events):
        signal = "parse_error"
    elif not attempts:
        signal = "no_attempts"
    elif need_hints and not accepted:
        signal = "structured_feedback"

    return {
        "path": str(path),
        "name": path.name,
        "problem_id": problem_id,
        "mode": str(start.get("mode") or ""),
        "attempts": len(attempts),
        "prompts": len(prompts),
        "router_events": len(routers),
        "accepted": accepted,
        "accepted_tool": accepted_tool,
        "counterexample_size": counterexample_size,
        "false_model_source": false_model_source,
        "tools": tools,
        "statuses": statuses,
        "errors": errors,
        "need_hint_count": len(need_hints),
        "last_need_hint": _as_dict(need_hints[-1]) if need_hints else {},
        "signal": signal,
    }


def _expand_paths(patterns: list[str]) -> list[Path]:
    paths: list[Path] = []
    seen: set[Path] = set()
    for pattern in patterns:
        matches = glob.glob(pattern)
        if not matches:
            candidate = Path(pattern)
            if candidate.exists():
                matches = [str(candidate)]
        for match in matches:
            path = Path(match)
            if path.is_dir():
                for child in path.glob("*.jsonl"):
                    resolved = child.resolve()
                    if resolved not in seen:
                        seen.add(resolved)
                        paths.append(child)
            elif path.suffix == ".jsonl":
                resolved = path.resolve()
                if resolved not in seen:
                    seen.add(resolved)
                    paths.append(path)
    return sorted(paths, key=lambda item: str(item))


def _print_markdown(rows: list[dict[str, Any]], *, max_rows: int) -> None:
    tool_counts: Counter[str] = Counter()
    tool_accepts: Counter[str] = Counter()
    signal_counts: Counter[str] = Counter(row["signal"] for row in rows)
    error_counts: Counter[str] = Counter()
    by_problem: dict[str, list[dict[str, Any]]] = defaultdict(list)

    for row in rows:
        by_problem[row["problem_id"]].append(row)
        for tool in row["tools"]:
            tool_counts[tool] += 1
        if row["accepted"] and row["accepted_tool"]:
            tool_accepts[row["accepted_tool"]] += 1
        for error in row["errors"]:
            error_counts[error] += 1

    print("# Sidecar Scoreboard\n")
    print(f"Transcripts: {len(rows)}")
    print(f"Accepted transcripts: {sum(1 for row in rows if row['accepted'])}")
    print(f"Problems: {len(by_problem)}")
    print("")

    print("## Signals\n")
    print("| Signal | Count |")
    print("|---|---:|")
    for signal, count in signal_counts.most_common():
        print(f"| {signal} | {count} |")
    print("")

    print("## Tools\n")
    print("| Tool | Calls | Accepted transcripts |")
    print("|---|---:|---:|")
    for tool, count in tool_counts.most_common():
        print(f"| {tool} | {count} | {tool_accepts.get(tool, 0)} |")
    print("")

    if error_counts:
        print("## Top Errors\n")
        print("| Error | Count |")
        print("|---|---:|")
        for error, count in error_counts.most_common(12):
            print(f"| `{error}` | {count} |")
        print("")

    print("## Transcript Rows\n")
    print("| Problem | Mode | Signal | Attempts | Tools | Last error | Last need | File |")
    print("|---|---|---|---:|---|---|---|---|")
    for row in rows[:max_rows]:
        tools = ", ".join(row["tools"][-5:])
        last_error = row["errors"][-1] if row["errors"] else ""
        need = _short(row["last_need_hint"].get("need_hint"), limit=80)
        print(
            "| "
            + " | ".join([
                row["problem_id"],
                row["mode"],
                row["signal"],
                str(row["attempts"]),
                _short(tools, limit=80),
                f"`{last_error}`" if last_error else "",
                need,
                row["name"],
            ])
            + " |"
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "paths",
        nargs="*",
        help="Transcript files, globs, or directories. Defaults to sidecar_runs/*.jsonl.",
    )
    parser.add_argument("--json", action="store_true", help="Emit machine-readable JSON instead of Markdown.")
    parser.add_argument("--max-rows", type=int, default=80, help="Maximum transcript rows in Markdown output.")
    parser.add_argument("--accepted-only", action="store_true", help="Only show accepted transcripts.")
    parser.add_argument("--problem", action="append", default=[], help="Filter to a problem id; repeatable.")
    args = parser.parse_args()

    patterns = args.paths or [str(ROOT / "sidecar_runs" / "*.jsonl")]
    rows = [summarize_transcript(path) for path in _expand_paths(patterns)]
    if args.problem:
        wanted = set(args.problem)
        rows = [row for row in rows if row["problem_id"] in wanted]
    if args.accepted_only:
        rows = [row for row in rows if row["accepted"]]

    rows = sorted(rows, key=lambda row: (row["problem_id"], row["name"]))
    if args.json:
        print(json.dumps({"transcripts": rows}, indent=2, ensure_ascii=False))
    else:
        _print_markdown(rows, max_rows=args.max_rows)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
