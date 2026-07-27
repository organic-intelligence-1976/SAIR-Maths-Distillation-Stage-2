#!/usr/bin/env python3
"""Reject benchmark-identity dispatch in the packed submission source."""

from __future__ import annotations

import argparse
import ast
import json
import re
from pathlib import Path
from typing import Any


BENCHMARK_NAME = re.compile(
    r"\b(?:hard[123]|normal|evaluation_order\d*)_\d+\b",
    re.IGNORECASE,
)
KNOWN_LABEL_FIELD = re.compile(r"""["']answer["']""")
FORBIDDEN_MARKERS = (
    "KNOWN_IMPLICATION_SEMANTICS",
    "VERIFIED_SYMBOLIC_MODEL_ARTIFACTS",
    "verified_symbolic_model_artifact",
    "memory:verified",
)
SENSITIVE_VARIABLES = {
    "problem_id",
    "eq1_id",
    "eq2_id",
    "equation_id",
    "answer",
}
SENSITIVE_FIELD_STRINGS = {"id", *SENSITIVE_VARIABLES}


def sensitive_references(node: ast.AST) -> list[str]:
    references: list[str] = []
    for child in ast.walk(node):
        if isinstance(child, ast.Name) and child.id in SENSITIVE_VARIABLES:
            references.append(child.id)
        elif isinstance(child, ast.Attribute) and child.attr in SENSITIVE_VARIABLES:
            references.append(child.attr)
        elif isinstance(child, ast.Constant) and child.value in SENSITIVE_FIELD_STRINGS:
            references.append(str(child.value))
    return sorted(set(references))


class SensitiveBranchVisitor(ast.NodeVisitor):
    def __init__(self) -> None:
        self.findings: list[dict[str, Any]] = []

    def inspect_test(self, node: ast.AST, kind: str) -> None:
        references = sensitive_references(node)
        if references:
            self.findings.append({
                "line": getattr(node, "lineno", None),
                "kind": kind,
                "identity_references": references,
            })

    def visit_If(self, node: ast.If) -> None:
        self.inspect_test(node.test, "if")
        self.generic_visit(node)

    def visit_IfExp(self, node: ast.IfExp) -> None:
        self.inspect_test(node.test, "if_expression")
        self.generic_visit(node)

    def visit_While(self, node: ast.While) -> None:
        self.inspect_test(node.test, "while")
        self.generic_visit(node)

    def visit_Match(self, node: ast.Match) -> None:
        self.inspect_test(node.subject, "match")
        self.generic_visit(node)


def audit_source(path: Path) -> dict[str, Any]:
    source = path.read_text(encoding="utf-8")
    benchmark_names = sorted(set(BENCHMARK_NAME.findall(source)))
    known_label_fields = KNOWN_LABEL_FIELD.findall(source)
    forbidden_markers = [
        marker for marker in FORBIDDEN_MARKERS if marker in source
    ]
    syntax_error = None
    sensitive_branches: list[dict[str, Any]] = []
    try:
        tree = ast.parse(source, filename=str(path))
    except SyntaxError as exc:
        syntax_error = {
            "line": exc.lineno,
            "offset": exc.offset,
            "message": exc.msg,
        }
    else:
        visitor = SensitiveBranchVisitor()
        visitor.visit(tree)
        sensitive_branches = visitor.findings
    checks = {
        "syntax_valid": syntax_error is None,
        "no_benchmark_names": not benchmark_names,
        "no_exact_case_symbols": not forbidden_markers,
        "no_known_label_reads": not known_label_fields,
        "no_sensitive_field_branches": not sensitive_branches,
    }
    return {
        "source": str(path),
        "checks": checks,
        "passed": all(checks.values()),
        "benchmark_names": benchmark_names,
        "forbidden_markers": forbidden_markers,
        "known_label_fields": known_label_fields,
        "sensitive_branches": sensitive_branches,
        "syntax_error": syntax_error,
        "policy": (
            "The submission may inspect equation syntax and term structure, "
            "but known labels and benchmark identifiers cannot select "
            "algorithms or artifacts."
        ),
    }


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "source",
        nargs="?",
        type=Path,
        default=root / "baby_solver.py",
    )
    args = parser.parse_args()
    result = audit_source(args.source.resolve())
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
