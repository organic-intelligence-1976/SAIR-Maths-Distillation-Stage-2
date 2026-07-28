#!/usr/bin/env python3
"""Run the submission over the full reference corpus and retain Lean certificates."""

from __future__ import annotations

import argparse
import json
import re
import sys
import threading
import time
import traceback
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
OFFICIAL = ROOT / "official-stage2"
sys.path.insert(0, str(OFFICIAL))

from pipeline.proxy import load_config, load_problems, run_solver  # type: ignore  # noqa: E402


DEFAULT_PROBLEM_FILES = (
    OFFICIAL / "examples" / "problems" / "normal.jsonl",
    OFFICIAL / "examples" / "problems" / "hard1.jsonl",
    OFFICIAL / "examples" / "problems" / "hard2.jsonl",
    OFFICIAL / "examples" / "problems" / "hard3.jsonl",
)
SAFE_ID = re.compile(r"[^A-Za-z0-9_.-]+")


def safe_id(value: str) -> str:
    return SAFE_ID.sub("_", value)


def atomic_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def load_reference_corpus(paths: list[Path]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    seen: set[str] = set()
    for path in paths:
        dataset = path.stem
        for problem in load_problems(str(path)):
            problem_id = str(problem["id"])
            if problem_id in seen:
                raise ValueError(f"duplicate problem id across corpus: {problem_id}")
            seen.add(problem_id)
            rows.append({**problem, "_dataset": dataset})
    return rows


def result_path(output_root: Path, problem_id: str) -> Path:
    return output_root / "results" / f"{safe_id(problem_id)}.json"


def certificate_path(output_root: Path, problem_id: str) -> Path:
    return output_root / "certificates" / f"{safe_id(problem_id)}.lean"


def load_record(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return value if isinstance(value, dict) else None


def lean_certificate(problem: dict[str, Any], result: dict[str, Any]) -> str:
    code = str(result["code"]).strip()
    header = "\n".join([
        "/-",
        "SAIR Mathematics Distillation Stage 2 verified certificate",
        f"Problem: {problem['id']}",
        f"Implication: {problem['equation1']}  -->  {problem['equation2']}",
        f"Verdict: {result['verdict']}",
        "Verification: accepted by the official Lean proxy/judge",
        "-/",
        "",
    ])
    return header + code + "\n"


def llm_health(log: Any) -> dict[str, Any]:
    events = log if isinstance(log, list) else []
    responses = [
        event.get("response") or {}
        for event in events
        if isinstance(event, dict) and event.get("type") == "llm"
    ]
    errors = [
        str(response.get("error"))
        for response in responses
        if response.get("error")
    ]
    return {
        "llm_successful_responses": len(responses) - len(errors),
        "llm_error_count": len(errors),
        "llm_error_messages": list(dict.fromkeys(errors))[:3],
    }


def compact_result(result: dict[str, Any]) -> dict[str, Any]:
    log = result.get("log")
    return {
        "solved": bool(result.get("solved")),
        "verdict": result.get("verdict"),
        "code": result.get("code"),
        "llm_calls": result.get("llm_calls"),
        "judge_calls": result.get("judge_calls"),
        "timed_out": result.get("timed_out"),
        "log": log,
        "stderr_tail": result.get("stderr_tail"),
        **llm_health(log),
    }


def run_one(
    submission_dir: Path,
    problem: dict[str, Any],
    config: dict[str, Any],
    output_root: Path,
    timeout_seconds: int,
) -> dict[str, Any]:
    started = time.time()
    try:
        raw_result = run_solver(submission_dir, problem, config)
        result = compact_result(raw_result)
        error = None
    except Exception as exc:  # preserve the rest of a long batch
        result = {
            "solved": False,
            "verdict": None,
            "code": None,
            "llm_calls": None,
            "judge_calls": None,
            "timed_out": False,
            "log": [],
            "stderr_tail": None,
        }
        error = {
            "type": type(exc).__name__,
            "message": str(exc),
            "traceback": traceback.format_exc(limit=12),
        }
    elapsed = round(time.time() - started, 3)
    path = result_path(output_root, str(problem["id"]))
    previous = load_record(path) or {
        "problem": {
            "id": problem["id"],
            "dataset": problem["_dataset"],
            "eq1_id": problem["eq1_id"],
            "eq2_id": problem["eq2_id"],
            "equation1": problem["equation1"],
            "equation2": problem["equation2"],
            "expected_answer": problem.get("answer"),
        },
        "attempts": [],
    }
    attempt = {
        "started_at": time.strftime(
            "%Y-%m-%dT%H:%M:%SZ",
            time.gmtime(started),
        ),
        "timeout_seconds": timeout_seconds,
        "elapsed_seconds": elapsed,
        "error": error,
        **result,
    }
    previous.setdefault("attempts", []).append(attempt)
    previous["latest"] = attempt
    previous["solved"] = bool(result["solved"])
    previous["verdict"] = result.get("verdict")
    previous["certificate"] = None
    expected = problem.get("answer")
    expected_verdict = (
        "true" if expected is True else "false" if expected is False else None
    )
    previous["expected_matches"] = (
        result.get("verdict") == expected_verdict
        if result["solved"] and expected_verdict is not None
        else None
    )
    if result["solved"] and isinstance(result.get("code"), str):
        cert_path = certificate_path(output_root, str(problem["id"]))
        cert_path.parent.mkdir(parents=True, exist_ok=True)
        cert_path.write_text(
            lean_certificate(problem, result),
            encoding="utf-8",
        )
        previous["certificate"] = str(cert_path)
    atomic_json(path, previous)
    return {
        "id": problem["id"],
        "dataset": problem["_dataset"],
        "solved": previous["solved"],
        "verdict": previous["verdict"],
        "expected_matches": previous["expected_matches"],
        "elapsed_seconds": elapsed,
        "llm_calls": result.get("llm_calls"),
        "llm_successful_responses": result.get("llm_successful_responses"),
        "llm_error_count": result.get("llm_error_count"),
        "llm_error_messages": result.get("llm_error_messages"),
        "judge_calls": result.get("judge_calls"),
        "timed_out": result.get("timed_out"),
        "error": error,
        "result_path": str(path),
        "certificate": previous["certificate"],
    }


def summarize(
    problems: list[dict[str, Any]],
    output_root: Path,
    *,
    timeout_seconds: int,
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for problem in problems:
        record = load_record(result_path(output_root, str(problem["id"])))
        latest = (record or {}).get("latest") or {}
        rows.append({
            "id": problem["id"],
            "dataset": problem["_dataset"],
            "solved": bool((record or {}).get("solved")),
            "verdict": (record or {}).get("verdict"),
            "expected_matches": (record or {}).get("expected_matches"),
            "attempt_count": len((record or {}).get("attempts") or []),
            "largest_timeout_seconds": max(
                [
                    int(attempt.get("timeout_seconds") or 0)
                    for attempt in (record or {}).get("attempts") or []
                ]
                or [0]
            ),
            "elapsed_seconds": latest.get("elapsed_seconds"),
            "llm_calls": latest.get("llm_calls"),
            "llm_successful_responses": latest.get("llm_successful_responses"),
            "llm_error_count": latest.get("llm_error_count"),
            "llm_error_messages": latest.get("llm_error_messages"),
            "judge_calls": latest.get("judge_calls"),
            "timed_out": latest.get("timed_out"),
            "error": latest.get("error"),
            "certificate": (record or {}).get("certificate"),
        })
    solved = [row for row in rows if row["solved"]]
    unresolved = [row for row in rows if not row["solved"]]
    mismatches = [
        row for row in solved if row.get("expected_matches") is False
    ]
    by_dataset: dict[str, dict[str, int]] = {}
    for dataset in sorted({row["dataset"] for row in rows}):
        subset = [row for row in rows if row["dataset"] == dataset]
        by_dataset[dataset] = {
            "total": len(subset),
            "solved": sum(bool(row["solved"]) for row in subset),
            "unresolved": sum(not row["solved"] for row in subset),
        }
    return {
        "updated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "output_root": str(output_root),
        "requested_timeout_seconds": timeout_seconds,
        "total": len(rows),
        "solved": len(solved),
        "unresolved": len(unresolved),
        "certificates": sum(bool(row["certificate"]) for row in rows),
        "verdicts": dict(Counter(row["verdict"] for row in solved)),
        "expected_mismatches": mismatches,
        "by_dataset": by_dataset,
        "unresolved_problems": unresolved,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--submission-dir",
        type=Path,
        default=ROOT / "submission",
    )
    parser.add_argument(
        "--problem-file",
        action="append",
        type=Path,
        dest="problem_files",
        help="Repeat to override the normal+hard1+hard2+hard3 corpus.",
    )
    parser.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".artifacts" / "full_verification",
    )
    parser.add_argument(
        "--config",
        type=Path,
        default=OFFICIAL / "pipeline" / "config.json",
    )
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument(
        "--timeout-seconds",
        type=int,
        default=3600,
        help="Per-problem solver budget; unresolved cases can be retried later.",
    )
    parser.add_argument(
        "--limit",
        type=int,
        help="Run only the first N currently unresolved problems.",
    )
    parser.add_argument("--progress-every", type=int, default=10)
    args = parser.parse_args()

    problem_files = [
        path.resolve()
        for path in (args.problem_files or list(DEFAULT_PROBLEM_FILES))
    ]
    problems = load_reference_corpus(problem_files)
    args.output_root.mkdir(parents=True, exist_ok=True)

    pending: list[dict[str, Any]] = []
    for problem in problems:
        previous = load_record(
            result_path(args.output_root, str(problem["id"]))
        )
        if previous and previous.get("solved"):
            continue
        pending.append(problem)
    if args.limit is not None:
        pending = pending[: max(0, args.limit)]

    config = load_config(str(args.config))
    config["solver"]["timeout_seconds"] = max(1, args.timeout_seconds)
    summary_lock = threading.Lock()
    completed = 0
    started = time.time()
    print(json.dumps({
        "event": "start",
        "corpus_size": len(problems),
        "pending": len(pending),
        "workers": max(1, args.workers),
        "timeout_seconds": config["solver"]["timeout_seconds"],
        "output_root": str(args.output_root),
        "problem_files": [str(path) for path in problem_files],
    }, ensure_ascii=False), flush=True)

    with ThreadPoolExecutor(max_workers=max(1, args.workers)) as pool:
        futures = {
            pool.submit(
                run_one,
                args.submission_dir.resolve(),
                problem,
                config,
                args.output_root.resolve(),
                config["solver"]["timeout_seconds"],
            ): problem
            for problem in pending
        }
        for future in as_completed(futures):
            row = future.result()
            with summary_lock:
                completed += 1
                if (
                    not row["solved"]
                    or completed % max(1, args.progress_every) == 0
                    or completed == len(pending)
                ):
                    print(json.dumps({
                        "event": "progress",
                        "completed": completed,
                        "pending_this_run": len(pending),
                        "wall_seconds": round(time.time() - started, 1),
                        **row,
                    }, ensure_ascii=False), flush=True)
                summary = summarize(
                    problems,
                    args.output_root.resolve(),
                    timeout_seconds=config["solver"]["timeout_seconds"],
                )
                atomic_json(args.output_root / "summary.json", summary)

    summary = summarize(
        problems,
        args.output_root.resolve(),
        timeout_seconds=config["solver"]["timeout_seconds"],
    )
    summary["run_wall_seconds"] = round(time.time() - started, 3)
    atomic_json(args.output_root / "summary.json", summary)
    print(json.dumps({"event": "complete", **summary}, ensure_ascii=False), flush=True)
    return 0 if summary["unresolved"] == 0 and not summary["expected_mismatches"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
