"""Select verified research products that may enter a competition build."""

from __future__ import annotations

from typing import Any, Iterable


class IntegrationCatalog:
    """Minimal promotion gate; compilation remains separate from discovery."""

    @staticmethod
    def select_competition_candidates(artifacts: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
        selected = []
        for artifact in artifacts:
            if artifact.get("status") != "verified":
                continue
            if artifact.get("deployability") != "competition_candidate":
                continue
            selected.append(artifact)
        return selected

    @staticmethod
    def promotion_report(artifacts: Iterable[dict[str, Any]]) -> dict[str, Any]:
        rows = list(artifacts)
        selected = IntegrationCatalog.select_competition_candidates(rows)
        return {
            "artifact_count": len(rows),
            "selected_count": len(selected),
            "selected_ids": [row.get("artifact_id") for row in selected],
            "excluded": [
                {
                    "artifact_id": row.get("artifact_id"),
                    "status": row.get("status"),
                    "deployability": row.get("deployability"),
                }
                for row in rows
                if row not in selected
            ],
        }

