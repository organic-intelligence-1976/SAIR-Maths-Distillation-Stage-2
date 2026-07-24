"""Finite/general implication classification backed by audited local data."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from .protocol import ProblemSpec, SemanticRecord


class SemanticService:
    def __init__(self, registry_path: Path):
        self.registry_path = registry_path
        registry = json.loads(registry_path.read_text(encoding="utf-8"))
        self.registry_source = registry.get("source") or {}
        self.austin_pairs = {
            (int(row["eq1_id"]), int(row["eq2_id"]))
            for row in registry.get("pairs") or []
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
        if pair == (677, 255):
            return SemanticRecord(
                semantic_class="open_finite_implication",
                semantic_target="finite_implication",
                general_status="false",
                finite_status="unknown",
                certificate_class="finite_model_or_finite_structure_proof",
                source="ETP Equation 677 chapter",
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

