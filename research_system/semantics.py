"""Finite/general implication classification backed by audited local data."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from .protocol import ProblemSpec, SemanticRecord


class SemanticService:
    def __init__(
        self,
        registry_path: Path,
        status_overrides_path: Path | None = None,
    ):
        self.registry_path = registry_path
        registry = json.loads(registry_path.read_text(encoding="utf-8"))
        self.registry_source = registry.get("source") or {}
        self.austin_pairs = {
            (int(row["eq1_id"]), int(row["eq2_id"]))
            for row in registry.get("pairs") or []
        }
        override_path = (
            status_overrides_path
            if status_overrides_path is not None
            else registry_path.with_name("implication_status_overrides.json")
        )
        override_rows: list[dict[str, Any]] = []
        if override_path.exists():
            override_data = json.loads(override_path.read_text(encoding="utf-8"))
            override_rows = [
                row
                for row in override_data.get("records") or []
                if isinstance(row, dict)
            ]
        self.status_overrides = {
            (int(row["eq1_id"]), int(row["eq2_id"])): row
            for row in override_rows
        }

    def classify(self, problem: ProblemSpec | dict[str, Any]) -> SemanticRecord:
        item = problem if isinstance(problem, ProblemSpec) else ProblemSpec.from_mapping(problem)
        pair = (item.eq1_id, item.eq2_id)
        if pair in self.austin_pairs:
            return SemanticRecord(
                semantic_class="austin_implication",
                semantic_target="general_implication",
                general_status="false",
                finite_status="true",
                certificate_class="infinite_model",
                source="ETP Austin implication registry",
                details={"registry_source": self.registry_source},
            )
        override = self.status_overrides.get(pair)
        if override is not None:
            return SemanticRecord(
                semantic_class=str(override["semantic_class"]),
                semantic_target=str(override["semantic_target"]),
                general_status=str(override["general_status"]),
                finite_status=str(override["finite_status"]),
                certificate_class=str(override["certificate_class"]),
                source=str(override["source"]),
                details={
                    "status_record": {
                        key: value
                        for key, value in override.items()
                        if key not in {"eq1_id", "eq2_id"}
                    }
                },
            )
        general = "true" if item.answer is True else "false" if item.answer is False else "unknown"
        return SemanticRecord(
            semantic_class="competition_row",
            semantic_target="general_implication",
            general_status=general,
            finite_status="unknown",
            certificate_class="true_proof" if general == "true" else "finite_model",
            source="competition problem row",
        )

    @staticmethod
    def finite_search_allowed(record: SemanticRecord) -> bool:
        return record.finite_status != "true"
