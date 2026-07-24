#!/usr/bin/env python3
"""Rank budget-policy reports by verified solves, then time and committed budget."""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from research_system.budget import budget_policy_record  # noqa: E402


def allocation_budget(value: Any) -> float:
    if isinstance(value, dict):
        if value.get("kind") == "renewable_budget_broker":
            return float(value.get("committed_budget") or 0.0)
        return sum(allocation_budget(item) for item in value.values())
    if isinstance(value, list):
        return sum(allocation_budget(item) for item in value)
    return 0.0


def report_episodes(payload: dict[str, Any]) -> list[dict[str, Any]]:
    episodes = []
    for report in payload.get("reports") or []:
        if not isinstance(report, dict):
            continue
        curriculum = report.get("curriculum")
        episode = curriculum.get("episode") if isinstance(curriculum, dict) else None
        if isinstance(episode, dict):
            episodes.append(episode)
    return episodes


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("reports", nargs="+", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    aggregate: dict[str, dict[str, Any]] = defaultdict(lambda: {
        "reports": [],
        "cases": 0,
        "accepted": 0,
        "seconds": 0.0,
        "committed_budget": 0.0,
    })
    for path in args.reports:
        payload = json.loads(path.read_text(encoding="utf-8"))
        record = payload.get("budget_policy")
        if isinstance(record, dict) and isinstance(record.get("budget_policy"), dict):
            normalized = budget_policy_record(record["budget_policy"])
        else:
            episodes = report_episodes(payload)
            raw = next(
                (
                    episode.get("metadata", {}).get("budget_policy")
                    for episode in episodes
                    if isinstance(episode.get("metadata"), dict)
                    and isinstance(episode.get("metadata", {}).get("budget_policy"), dict)
                ),
                None,
            )
            normalized = budget_policy_record(raw)
        policy_id = normalized["policy_id"]
        row = aggregate[policy_id]
        row["policy_id"] = policy_id
        row["budget_policy"] = normalized["budget_policy"]
        row["reports"].append(str(path))
        episodes = report_episodes(payload)
        row["cases"] += len(episodes)
        row["accepted"] += sum(bool(episode.get("accepted")) for episode in episodes)
        row["seconds"] += sum(float(episode.get("seconds") or 0.0) for episode in episodes)
        row["committed_budget"] += allocation_budget(episodes)

    rankings = sorted(
        aggregate.values(),
        key=lambda row: (-row["accepted"], row["seconds"], row["committed_budget"], row["policy_id"]),
    )
    for rank, row in enumerate(rankings, start=1):
        row["rank"] = rank
        row["solve_rate"] = round(row["accepted"] / max(1, row["cases"]), 6)
        row["seconds"] = round(row["seconds"], 6)
        row["committed_budget"] = round(row["committed_budget"], 6)
    output = {"ranking_rule": ["accepted desc", "seconds asc", "committed_budget asc"], "policies": rankings}
    text = json.dumps(output, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(json.dumps({
        "output": str(args.output) if args.output else None,
        "ranking": [
            {
                "rank": row["rank"],
                "policy_id": row["policy_id"],
                "accepted": row["accepted"],
                "cases": row["cases"],
                "seconds": row["seconds"],
            }
            for row in rankings
        ],
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
