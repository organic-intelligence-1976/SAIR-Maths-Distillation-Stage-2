"""Append-only episode/artifact ledger with minimal structural retrieval."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Iterable

from .protocol import EpisodeRecord, StrategyArtifact
from .structure import (
    canonical_equation_signature,
    dual_equation,
    plan_node_signatures,
    problem_structure,
    structural_similarity,
)


class ExperienceStore:
    def __init__(self, root: Path):
        self.root = root
        self.episodes_path = root / "episodes.jsonl"
        self.artifacts_path = root / "artifacts.jsonl"

    @staticmethod
    def _append(path: Path, row: dict[str, Any]) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")

    @staticmethod
    def _rows(path: Path) -> Iterable[dict[str, Any]]:
        if not path.exists():
            return []
        rows: list[dict[str, Any]] = []
        for line in path.read_text(encoding="utf-8").splitlines():
            if line.strip():
                rows.append(json.loads(line))
        return rows

    def append_episode(self, episode: EpisodeRecord) -> None:
        self._append(self.episodes_path, episode.to_mapping())

    def append_artifact(self, artifact: StrategyArtifact) -> None:
        self._append(self.artifacts_path, artifact.to_mapping())

    def retrieve_artifacts(
        self,
        *,
        kind: str | None = None,
        semantic_class: str | None = None,
        problem: Any = None,
        capability_mask: dict[str, Any] | None = None,
        blackboard: dict[str, Any] | None = None,
        min_structural_score: float = 35.0,
        limit: int = 8,
    ) -> list[dict[str, Any]]:
        """Retrieve verified artifacts with transparent structural attribution.

        Callers without a problem retain the original semantic-class lookup.
        Structural callers never fall back to problem IDs or transcript text.
        """
        query_structure = problem_structure(problem) if problem is not None else None
        query_disabled = sorted(str(item) for item in (capability_mask or {}).get("disabled", []))
        trusted_signatures = {
            canonical_equation_signature(str(node["equation"]))
            for node in (blackboard or {}).get("trusted_nodes", [])
            if isinstance(node, dict) and isinstance(node.get("equation"), str)
        }
        matches: list[tuple[float, int, dict[str, Any]]] = []
        rows = list(self._rows(self.artifacts_path))
        for recency, row in enumerate(reversed(rows)):
            if row.get("status") != "verified":
                continue
            if kind is not None and row.get("kind") != kind:
                continue
            trigger = row.get("trigger") if isinstance(row.get("trigger"), dict) else {}
            if (
                query_structure is None
                and semantic_class is not None
                and trigger.get("semantic_class") != semantic_class
            ):
                continue
            if query_structure is None:
                matches.append((0.0, recency, dict(row)))
                continue

            candidate_structure = trigger.get("problem_structure")
            score, reasons = structural_similarity(
                query_structure,
                candidate_structure if isinstance(candidate_structure, dict) else {},
            )
            if semantic_class is not None and trigger.get("semantic_class") == semantic_class:
                score += 2.0
                reasons.append("same_semantic_class")
            candidate_capability = trigger.get("capability_context")
            candidate_disabled = sorted(
                str(item)
                for item in (candidate_capability or {}).get("disabled", [])
            ) if isinstance(candidate_capability, dict) else []
            if query_disabled == candidate_disabled:
                score += 2.0
                reasons.append("same_capability_mask")

            plan_transform = "identity"
            if (
                isinstance(candidate_structure, dict)
                and query_structure.get("pair_signature") == candidate_structure.get("dual_pair_signature")
                and query_structure.get("pair_signature") != candidate_structure.get("pair_signature")
            ):
                plan_transform = "magma_dual"
            if plan_transform == "magma_dual":
                payload = row.get("payload") if isinstance(row.get("payload"), dict) else {}
                nodes = payload.get("plan_nodes") if isinstance(payload.get("plan_nodes"), list) else []
                plan_signatures = [
                    canonical_equation_signature(dual_equation(str(node["equation"])))
                    for node in nodes
                    if isinstance(node, dict) and isinstance(node.get("equation"), str)
                ]
            else:
                plan_signatures = plan_node_signatures(row)
            overlap = [signature for signature in plan_signatures if signature in trusted_signatures]
            missing = [signature for signature in plan_signatures if signature not in trusted_signatures]
            if overlap:
                overlap_ratio = len(overlap) / max(1, len(plan_signatures))
                score += 12.0 + 8.0 * overlap_ratio
                reasons.append(f"verified_partial_plan_overlap:{overlap_ratio:.3f}")
            if score < float(min_structural_score):
                continue
            retrieved = dict(row)
            retrieved["_retrieval"] = {
                "score": round(score, 6),
                "reasons": reasons,
                "query_pair_signature": query_structure.get("pair_signature"),
                "matched_plan_node_signatures": overlap,
                "missing_plan_node_signatures": missing,
                "plan_transform": plan_transform,
            }
            matches.append((score, recency, retrieved))
        matches.sort(key=lambda item: (-item[0], item[1], str(item[2].get("artifact_id"))))
        return [row for _score, _recency, row in matches[:max(0, limit)]]

    def summary(self) -> dict[str, Any]:
        episodes = list(self._rows(self.episodes_path))
        artifacts = list(self._rows(self.artifacts_path))
        return {
            "root": str(self.root),
            "episode_count": len(episodes),
            "accepted_episode_count": sum(bool(row.get("accepted")) for row in episodes),
            "artifact_count": len(artifacts),
            "artifact_kinds": sorted({str(row.get("kind")) for row in artifacts}),
        }
