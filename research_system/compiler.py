"""Reproducible competition single-file build from modular source selections."""

from __future__ import annotations

import ast
import hashlib
import io
import json
import time
import tokenize
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import baby_solver


COMPILER_VERSION = "submission-compiler-v2"


@dataclass(frozen=True)
class CompilationSpec:
    source: Path
    submission_dir: Path
    manifest_path: Path
    max_solver_bytes: int = 500_000


class SubmissionCompiler:
    """Initial compiler backend using the packed solver as one deployable unit.

    The interface already models source selection, validation, provenance, and
    output layout.  Later modular competition-safe units can replace the legacy
    source unit without changing callers or the generated artifact contract.
    """

    required_top_level_names = {"PROMPT", "solve", "read_msg", "send_msg"}

    @staticmethod
    def _sha256(data: bytes) -> str:
        return hashlib.sha256(data).hexdigest()

    @staticmethod
    def _defined_names(tree: ast.Module) -> set[str]:
        names: set[str] = set()
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                names.add(node.name)
            elif isinstance(node, (ast.Assign, ast.AnnAssign)):
                targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                for target in targets:
                    if isinstance(target, ast.Name):
                        names.add(target.id)
        return names

    @staticmethod
    def _validate_layout(submission_dir: Path) -> str | None:
        entries = list(submission_dir.iterdir()) if submission_dir.exists() else []
        extras = sorted(entry.name for entry in entries if entry.name != "solver.py")
        if extras:
            return f"submission directory contains non-solver entries: {extras}"
        solver = submission_dir / "solver.py"
        if not solver.is_file() or solver.is_symlink():
            return "submission must contain one regular, non-symlink solver.py"
        return None

    @staticmethod
    def _docstring_spans(source: str) -> set[tuple[tuple[int, int], tuple[int, int]]]:
        """Return token spans for inert module, class, and function docstrings."""
        tree = ast.parse(source)
        scopes = [
            node for node in ast.walk(tree)
            if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))
        ]
        spans: set[tuple[tuple[int, int], tuple[int, int]]] = set()
        for scope in scopes:
            body = getattr(scope, "body", [])
            if not body:
                continue
            first = body[0]
            if not (
                isinstance(first, ast.Expr)
                and isinstance(first.value, ast.Constant)
                and isinstance(first.value.value, str)
            ):
                continue
            value = first.value
            spans.add(((value.lineno, value.col_offset), (value.end_lineno, value.end_col_offset)))
        return spans

    @staticmethod
    def _compact_token_pairs(
        source: str,
        docstring_spans: set[tuple[tuple[int, int], tuple[int, int]]],
    ) -> list[tuple[int, str]]:
        """Return version-stable token pairs while preserving f-strings exactly.

        Python 3.12+ exposes the internals of f-strings as separate tokenizer
        tokens. Passing those token pairs through ``untokenize`` can insert
        spaces that Python 3.11 rejects, for example ``{value !r }``. Collapse
        each complete f-string back to one string token before compaction so
        builds are identical on the development and competition interpreters.
        """
        tokens = list(tokenize.generate_tokens(io.StringIO(source).readline))
        source_lines = source.splitlines(keepends=True)
        line_offsets = [0]
        for line in source_lines:
            line_offsets.append(line_offsets[-1] + len(line))

        def source_slice(start: tuple[int, int], end: tuple[int, int]) -> str:
            start_offset = line_offsets[start[0] - 1] + start[1]
            end_offset = line_offsets[end[0] - 1] + end[1]
            return source[start_offset:end_offset]

        fstring_start = getattr(tokenize, "FSTRING_START", None)
        fstring_end = getattr(tokenize, "FSTRING_END", None)
        compact: list[tuple[int, str]] = []
        index = 0
        while index < len(tokens):
            token = tokens[index]
            if fstring_start is not None and token.type == fstring_start:
                depth = 0
                end_index = index
                while end_index < len(tokens):
                    candidate = tokens[end_index]
                    if candidate.type == fstring_start:
                        depth += 1
                    elif candidate.type == fstring_end:
                        depth -= 1
                        if depth == 0:
                            break
                    end_index += 1
                if depth != 0:
                    raise ValueError(f"unterminated f-string at line {token.start[0]}")
                compact.append((
                    tokenize.STRING,
                    source_slice(token.start, tokens[end_index].end),
                ))
                index = end_index + 1
                continue
            if (
                token.type != tokenize.COMMENT
                and not (token.type == tokenize.NL and not token.line.strip())
                and not (
                    token.type == tokenize.STRING
                    and (token.start, token.end) in docstring_spans
                )
            ):
                compact.append((token.type, token.string))
            index += 1
        return compact

    def compile(self, spec: CompilationSpec) -> dict[str, Any]:
        source_bytes = spec.source.read_bytes()
        source_text = source_bytes.decode("utf-8")
        source_tree = ast.parse(source_text, filename=str(spec.source))
        defined = self._defined_names(source_tree)
        missing = sorted(self.required_top_level_names - defined)
        if missing:
            raise ValueError(f"source is missing competition entry definitions: {missing}")
        prompt_nodes = [
            node
            for node in source_tree.body
            if isinstance(node, ast.Assign)
            and any(isinstance(target, ast.Name) and target.id == "PROMPT" for target in node.targets)
        ]
        if not prompt_nodes or not isinstance(prompt_nodes[0].value, ast.Constant) or not isinstance(prompt_nodes[0].value.value, str):
            raise ValueError("PROMPT must be a top-level string literal for AST extraction")

        lines = source_text.splitlines(keepends=True)
        shebang = lines[0] if lines and lines[0].startswith("#!") else ""
        token_source = "".join(lines[1:]) if shebang else source_text
        docstring_spans = self._docstring_spans(token_source)
        compact_tokens = self._compact_token_pairs(token_source, docstring_spans)
        compiled_source = tokenize.untokenize(compact_tokens)
        compiled_source = "".join(
            line.rstrip(" \t\r\n") + ("\n" if line.endswith(("\n", "\r")) else "")
            for line in compiled_source.splitlines(keepends=True)
        )
        header = [
            f"# Generated by {COMPILER_VERSION}; edit modular sources, not this artifact.\n",
            f"# Source: {spec.source.name} sha256={self._sha256(source_bytes)}\n",
        ]
        output_text = "".join([shebang, *header, compiled_source])
        output_bytes = output_text.encode("utf-8")
        if len(output_bytes) > spec.max_solver_bytes:
            raise ValueError(
                f"compiled solver is {len(output_bytes)} bytes; limit is {spec.max_solver_bytes}"
            )
        ast.parse(output_text, filename="solver.py")

        spec.submission_dir.mkdir(parents=True, exist_ok=True)
        existing_extras = [entry for entry in spec.submission_dir.iterdir() if entry.name != "solver.py"]
        if existing_extras:
            raise ValueError(
                "refusing to compile into a submission directory containing extras: "
                + repr(sorted(entry.name for entry in existing_extras))
            )
        output_path = spec.submission_dir / "solver.py"
        output_path.write_text(output_text, encoding="utf-8")
        layout_error = self._validate_layout(spec.submission_dir)
        if layout_error:
            raise ValueError(layout_error)

        tool_rows = baby_solver.capability_manifest()["tools"]
        capability_ids = [row["capability"] for row in tool_rows]
        default_active = [row["capability"] for row in tool_rows]
        manifest = {
            "schema_version": 1,
            "compiler_version": COMPILER_VERSION,
            "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "mode": "legacy_packed_source_unit",
            "source": {
                "path": str(spec.source),
                "sha256": self._sha256(source_bytes),
                "bytes": len(source_bytes),
            },
            "output": {
                "path": str(output_path),
                "sha256": self._sha256(output_bytes),
                "bytes": len(output_bytes),
                "max_bytes": spec.max_solver_bytes,
                "layout_valid": True,
                "ast_valid": True,
                "prompt_literal_valid": True,
            },
            "included_capability_ids": capability_ids,
            "default_active_capability_ids": default_active,
            "policy_sensitive_capability_ids": ["tool:infinite_model_artifact"],
            "policy_sensitive_capability_note": (
                "The v1 legacy packed source includes an infinite-model artifact "
                "adapter. It is activated only for audited finite-true/general-false "
                "semantic cases, blocks finite-table search, and still relies on the "
                "official Lean judge as the trust boundary."
            ),
            "required_top_level_names": sorted(self.required_top_level_names),
        }
        spec.manifest_path.parent.mkdir(parents=True, exist_ok=True)
        spec.manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        return manifest
