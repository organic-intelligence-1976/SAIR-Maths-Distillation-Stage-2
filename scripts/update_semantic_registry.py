#!/usr/bin/env python3
"""Fetch, source-stamp, and audit the ETP Austin implication registry."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import time
import urllib.request
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = "teorth/equational_theories"
SOURCE_PATH = "data/Austin_implications.txt"
COMMIT_API = f"https://api.github.com/repos/{REPOSITORY}/commits/main"
PAIR_RE = re.compile(r"^Equation(\d+)\s+→\s+Equation(\d+)$")


def fetch_bytes(url: str) -> bytes:
    request = urllib.request.Request(url, headers={"User-Agent": "SAIR-research-semantic-registry/1"})
    with urllib.request.urlopen(request, timeout=30) as response:
        return response.read()


def upstream_commit() -> str:
    payload = json.loads(fetch_bytes(COMMIT_API).decode("utf-8"))
    commit = str(payload.get("sha") or "")
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("GitHub commit response did not contain a full SHA")
    return commit


def parse_pairs(raw: bytes) -> list[dict[str, int]]:
    pairs: list[dict[str, int]] = []
    for line_number, raw_line in enumerate(raw.decode("utf-8").splitlines(), 1):
        line = raw_line.strip()
        if not line:
            continue
        match = PAIR_RE.fullmatch(line)
        if not match:
            raise ValueError(f"unrecognized Austin-pair row {line_number}: {line!r}")
        pairs.append({"eq1_id": int(match.group(1)), "eq2_id": int(match.group(2))})
    if len(pairs) != len({(row["eq1_id"], row["eq2_id"]) for row in pairs}):
        raise ValueError("Austin registry contains duplicate pairs")
    return pairs


def iter_public_rows() -> list[dict[str, Any]]:
    problem_dir = ROOT / "official-stage2" / "examples" / "problems"
    rows: list[dict[str, Any]] = []
    seen: set[str] = set()
    for source in sorted(problem_dir.glob("*.jsonl")):
        if source.name.startswith("evaluation_"):
            continue
        for raw_line in source.read_text(encoding="utf-8").splitlines():
            if not raw_line.strip():
                continue
            row = json.loads(raw_line)
            problem_id = str(row.get("id") or "")
            if not problem_id or problem_id in seen:
                continue
            seen.add(problem_id)
            rows.append({**row, "source_file": str(source.relative_to(ROOT))})
    return rows


def public_audit(registry: dict[str, Any]) -> dict[str, Any]:
    pair_set = {(row["eq1_id"], row["eq2_id"]) for row in registry["pairs"]}
    rows = iter_public_rows()
    matches = []
    for row in rows:
        try:
            pair = (int(row["eq1_id"]), int(row["eq2_id"]))
        except (KeyError, TypeError, ValueError):
            continue
        if pair not in pair_set:
            continue
        matches.append({
            "id": row.get("id"),
            "eq1_id": pair[0],
            "eq2_id": pair[1],
            "equation1": row.get("equation1"),
            "equation2": row.get("equation2"),
            "competition_answer": row.get("answer"),
            "general_status": "false",
            "finite_status": "true",
            "certificate_class": "infinite_model",
            "source_file": row.get("source_file"),
        })
    return {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "registry_source": registry["source"],
        "public_rows_scanned": len(rows),
        "austin_rows_found": len(matches),
        "rows": matches,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "data" / "semantics" / "austin_implications.json",
    )
    parser.add_argument(
        "--audit-output",
        type=Path,
        default=ROOT / ".artifacts" / "public_semantic_audit.json",
    )
    parser.add_argument("--commit", help="Pin an upstream 40-character commit instead of resolving main")
    args = parser.parse_args()

    commit = args.commit or upstream_commit()
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("--commit must be a full 40-character lowercase SHA")
    raw_url = f"https://raw.githubusercontent.com/{REPOSITORY}/{commit}/{SOURCE_PATH}"
    raw = fetch_bytes(raw_url)
    pairs = parse_pairs(raw)
    if len(pairs) != 820:
        raise ValueError(f"expected 820 Austin implications, got {len(pairs)}")
    registry = {
        "schema_version": 1,
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "semantics": {
            "general_status": "false",
            "finite_status": "true",
            "certificate_class": "infinite_model",
        },
        "source": {
            "repository": f"https://github.com/{REPOSITORY}",
            "path": SOURCE_PATH,
            "commit": commit,
            "raw_url": raw_url,
            "sha256": hashlib.sha256(raw).hexdigest(),
        },
        "pair_count": len(pairs),
        "pairs": pairs,
    }
    audit = public_audit(registry)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.audit_output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(registry, indent=2) + "\n", encoding="utf-8")
    args.audit_output.write_text(json.dumps(audit, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({
        "output": str(args.output),
        "audit_output": str(args.audit_output),
        "commit": commit,
        "sha256": registry["source"]["sha256"],
        "pair_count": len(pairs),
        "public_rows_scanned": audit["public_rows_scanned"],
        "austin_rows_found": audit["austin_rows_found"],
        "austin_problem_ids": [row["id"] for row in audit["rows"]],
    }, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
