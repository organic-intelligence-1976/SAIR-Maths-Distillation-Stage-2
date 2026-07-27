#!/usr/bin/env python3
"""Build and statically validate a competition-compatible single solver.py."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from research_system.compiler import CompilationSpec, SubmissionCompiler  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=ROOT / "baby_solver.py")
    parser.add_argument(
        "--submission-dir",
        type=Path,
        default=ROOT / "submission",
    )
    parser.add_argument(
        "--manifest",
        type=Path,
        default=ROOT / ".artifacts" / "compiled_submission" / "build_manifest.json",
    )
    parser.add_argument("--max-solver-bytes", type=int, default=500_000)
    args = parser.parse_args()
    manifest = SubmissionCompiler().compile(CompilationSpec(
        source=args.source,
        submission_dir=args.submission_dir,
        manifest_path=args.manifest,
        max_solver_bytes=args.max_solver_bytes,
    ))
    print(json.dumps({
        "submission": manifest["output"]["path"],
        "manifest": str(args.manifest),
        "bytes": manifest["output"]["bytes"],
        "sha256": manifest["output"]["sha256"],
        "layout_valid": manifest["output"]["layout_valid"],
        "ast_valid": manifest["output"]["ast_valid"],
    }))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
