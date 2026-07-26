"""Versioned data contracts shared by the modular research components."""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from typing import Any


RESEARCH_PROTOCOL_VERSION = "sair-research-v1"


@dataclass(frozen=True)
class ProblemSpec:
    id: str
    eq1_id: int
    eq2_id: int
    equation1: str
    equation2: str
    answer: bool | None = None
    proof_policy: dict[str, Any] | None = None

    @classmethod
    def from_mapping(cls, data: dict[str, Any]) -> "ProblemSpec":
        return cls(
            id=str(data["id"]),
            eq1_id=int(data["eq1_id"]),
            eq2_id=int(data["eq2_id"]),
            equation1=str(data["equation1"]),
            equation2=str(data["equation2"]),
            answer=data.get("answer") if isinstance(data.get("answer"), bool) else None,
            proof_policy=data.get("proof_policy") if isinstance(data.get("proof_policy"), dict) else None,
        )

    def to_mapping(self) -> dict[str, Any]:
        return {key: value for key, value in asdict(self).items() if value is not None}


@dataclass(frozen=True)
class SemanticRecord:
    semantic_class: str
    semantic_target: str
    general_status: str
    finite_status: str
    certificate_class: str
    source: str
    details: dict[str, Any] = field(default_factory=dict)

    def to_mapping(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class ActionRequest:
    payload: dict[str, Any]
    origin: str = "planner"
    round_index: int = 1

    def to_mapping(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class ExecutionResult:
    status: str
    normalized_action: dict[str, Any] | None = None
    submitted_action: dict[str, Any] | None = None
    body: str | None = None
    finite_table: list[list[int]] | None = None
    infinite_code: str | None = None
    state: dict[str, Any] = field(default_factory=dict)
    adapter_state: dict[str, Any] | None = None
    seconds: float = 0.0

    @property
    def has_candidate(self) -> bool:
        return bool(self.body or self.finite_table is not None or self.infinite_code)

    def to_mapping(self, *, include_code: bool = False) -> dict[str, Any]:
        data = asdict(self)
        if not include_code:
            if self.body is not None:
                data["body"] = f"<Lean body: {len(self.body.encode('utf-8'))} bytes>"
            if self.infinite_code is not None:
                data["infinite_code"] = f"<Lean artifact: {len(self.infinite_code.encode('utf-8'))} bytes>"
        return data


@dataclass(frozen=True)
class VerificationRecord:
    status: str
    accepted: bool
    verdict: str
    profile: str
    message: str | None = None
    error_code: str | None = None
    seconds: float = 0.0
    details: dict[str, Any] = field(default_factory=dict)

    def to_mapping(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class StrategyArtifact:
    artifact_id: str
    kind: str
    status: str
    deployability: str
    trigger: dict[str, Any]
    payload: dict[str, Any]
    evidence: dict[str, Any]
    protocol_version: str = RESEARCH_PROTOCOL_VERSION

    def to_mapping(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class EpisodeRecord:
    episode_id: str
    case_id: str
    problem: dict[str, Any]
    semantics: dict[str, Any]
    capability_mask: dict[str, Any]
    planner: str
    split_label: str
    started_at: str
    attempts: list[dict[str, Any]] = field(default_factory=list)
    blackboard: dict[str, Any] = field(default_factory=dict)
    obligations: dict[str, Any] = field(default_factory=dict)
    verification: dict[str, Any] | None = None
    accepted: bool = False
    outcome: str = "running"
    seconds: float = 0.0
    metadata: dict[str, Any] = field(default_factory=dict)
    protocol_version: str = RESEARCH_PROTOCOL_VERSION

    @classmethod
    def from_mapping(cls, data: dict[str, Any]) -> "EpisodeRecord":
        return cls(
            episode_id=str(data["episode_id"]),
            case_id=str(data["case_id"]),
            problem=dict(data.get("problem") or {}),
            semantics=dict(data.get("semantics") or {}),
            capability_mask=dict(data.get("capability_mask") or {}),
            planner=str(data.get("planner") or "unknown"),
            split_label=str(data.get("split_label") or "development"),
            started_at=str(data.get("started_at") or ""),
            attempts=list(data.get("attempts") or []),
            blackboard=dict(data.get("blackboard") or {}),
            obligations=dict(data.get("obligations") or {}),
            verification=(
                dict(data["verification"])
                if isinstance(data.get("verification"), dict)
                else None
            ),
            accepted=bool(data.get("accepted")),
            outcome=str(data.get("outcome") or "running"),
            seconds=float(data.get("seconds") or 0.0),
            metadata=dict(data.get("metadata") or {}),
            protocol_version=str(data.get("protocol_version") or RESEARCH_PROTOCOL_VERSION),
        )

    def to_mapping(self) -> dict[str, Any]:
        return asdict(self)
