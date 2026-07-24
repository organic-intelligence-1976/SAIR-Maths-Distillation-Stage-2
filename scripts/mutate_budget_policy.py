#!/usr/bin/env python3
"""Generate reproducible offspring budget genotypes from one parent policy."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from research_system.budget import load_budget_policy, mutate_budget_policy  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--parent",
        type=Path,
        default=ROOT / "data" / "budget_policies" / "balanced_v1.json",
    )
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--count", type=int, default=8)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--sigma", type=float, default=0.25)
    args = parser.parse_args()

    parent = load_budget_policy(args.parent)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    records = []
    for offset in range(max(1, args.count)):
        child_seed = args.seed + offset
        child = mutate_budget_policy(parent, seed=child_seed, sigma=args.sigma)
        path = args.output_dir / f"{child['policy_id']}.json"
        path.write_text(json.dumps(child, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        records.append({"policy_id": child["policy_id"], "seed": child_seed, "path": str(path)})
    print(json.dumps({
        "parent": str(args.parent),
        "count": len(records),
        "offspring": records,
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
