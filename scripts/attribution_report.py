#!/usr/bin/env python3
"""Summarize the collaborative solver route attribution from pipeline runner JSON outputs.

The solver emits small stderr lines before each judge call:

    ATTRIBUTION {"event":"judge_attempt", "route":"...", ...}

The official proxy stores a bounded stderr tail in each result row. This script
correlates the Nth attribution line with the Nth judge call; for a solved row,
the attribution paired with the accepted judge call is the winning route.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path
from typing import Any


def load_rows(paths: list[str]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for raw_path in paths:
        path = Path(raw_path)
        data = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(data, list):
            raise ValueError(f"{path}: expected a JSON list from pipeline.runner")
        for row in data:
            if isinstance(row, dict):
                row = dict(row)
                row["_artifact"] = str(path)
                rows.append(row)
    return rows


def attribution_events(row: dict[str, Any]) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    for entry in row.get("log") or []:
        if entry.get("type") != "solver_stderr":
            continue
        for line in str(entry.get("tail") or "").splitlines():
            if not line.startswith("ATTRIBUTION "):
                continue
            payload = line[len("ATTRIBUTION "):]
            try:
                data = json.loads(payload)
            except json.JSONDecodeError:
                continue
            if isinstance(data, dict):
                events.append(data)
    return events


def judge_entries(row: dict[str, Any]) -> list[dict[str, Any]]:
    return [entry for entry in row.get("log") or [] if entry.get("type") == "judge"]


def accepted_judge_index(row: dict[str, Any]) -> int | None:
    for idx, entry in enumerate(judge_entries(row), start=1):
        if (entry.get("response") or {}).get("status") == "accepted":
            return idx
    return None


def classify_route(route: str | None, source: str | None) -> str:
    route = route or ""
    source = source or ""
    if route.startswith("llm:") or source.startswith("llm"):
        return "llm_load_bearing"
    if route.startswith("child_reference") or source == "reference_child_fallback":
        return "child_reference_fallback"
    if route.startswith("native_reference") or source == "reference_native_tool":
        return "native_reference_tool"
    if route.startswith("native:false"):
        return "native_false"
    if route.startswith("native:true"):
        return "native_true"
    if route:
        return "other_attributed"
    return "unknown"


def summarize_row(row: dict[str, Any]) -> dict[str, Any]:
    events = attribution_events(row)
    accepted_idx = accepted_judge_index(row)
    winning_event: dict[str, Any] | None = None
    if accepted_idx is not None and 0 <= accepted_idx - 1 < len(events):
        winning_event = events[accepted_idx - 1]
    elif row.get("solved") and events:
        winning_event = events[-1]
    route = winning_event.get("route") if winning_event else None
    source = winning_event.get("source") if winning_event else None
    detail = winning_event.get("detail") if winning_event else None
    return {
        "id": row.get("id"),
        "artifact": row.get("_artifact"),
        "solved": bool(row.get("solved")),
        "verdict": row.get("verdict"),
        "elapsed_seconds": row.get("elapsed_seconds"),
        "llm_calls": row.get("llm_calls"),
        "judge_calls": row.get("judge_calls"),
        "accepted_judge_index": accepted_idx,
        "attribution_events": len(events),
        "route": route,
        "source": source,
        "detail": detail,
        "category": classify_route(route, source),
        "attempted_routes": [
            {
                "route": event.get("route"),
                "source": event.get("source"),
                "verdict": event.get("verdict"),
                "detail": event.get("detail"),
                "category": classify_route(event.get("route"), event.get("source")),
            }
            for event in events
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Summarize solver route attribution from runner outputs.")
    parser.add_argument("results", nargs="+", help="pipeline.runner JSON output(s)")
    parser.add_argument("--json-output", default=None, help="Optional path for machine-readable summary")
    args = parser.parse_args()

    summaries = [summarize_row(row) for row in load_rows(args.results)]
    counts = Counter(row["category"] for row in summaries)
    solved_counts = Counter(row["category"] for row in summaries if row["solved"])

    print("Attribution Summary")
    print("===================")
    print(f"Rows: {len(summaries)}")
    print(f"Solved: {sum(1 for row in summaries if row['solved'])}")
    print()
    print("Solved by category:")
    for category, count in solved_counts.most_common():
        print(f"  {category}: {count}")
    print()
    print("All rows by category:")
    for category, count in counts.most_common():
        print(f"  {category}: {count}")
    print()
    print("Rows:")
    for row in summaries:
        mark = "OK" if row["solved"] else "--"
        print(
            f"  {mark} {row['id']}: {row['category']} route={row['route']} "
            f"verdict={row['verdict']} llm={row['llm_calls']} judge={row['judge_calls']}"
        )
        if not row["solved"] and row["attempted_routes"]:
            attempts = ", ".join(
                str(attempt["route"]) for attempt in row["attempted_routes"][-5:]
            )
            print(f"      attempted: {attempts}")
    child_rows = [row for row in summaries if row["solved"] and row["category"] == "child_reference_fallback"]
    unknown_solved = [row for row in summaries if row["solved"] and row["category"] == "unknown"]
    failed_child_attempts = [
        row for row in summaries
        if not row["solved"] and any(
            attempt["category"] == "child_reference_fallback"
            for attempt in row["attempted_routes"]
        )
    ]
    if child_rows or unknown_solved or failed_child_attempts:
        print()
        print("Action Queue:")
        for row in child_rows:
            print(f"  naturalize_child_route {row['id']}: {row['route']}")
        for row in unknown_solved:
            print(f"  rerun_for_attribution {row['id']}: no ATTRIBUTION line found")
        for row in failed_child_attempts:
            print(f"  inspect_failed_child_attempts {row['id']}: child fallback was tried but did not accept")

    if args.json_output:
        Path(args.json_output).write_text(json.dumps({
            "rows": summaries,
            "solved_by_category": dict(solved_counts),
            "all_by_category": dict(counts),
            "child_reference_winners": child_rows,
            "unknown_solved": unknown_solved,
            "failed_child_attempts": failed_child_attempts,
        }, indent=2, ensure_ascii=False), encoding="utf-8")


if __name__ == "__main__":
    main()
