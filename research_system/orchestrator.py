"""End-to-end verified episode orchestration."""

from __future__ import annotations

import hashlib
import json
import time
import uuid
from datetime import datetime, timezone
from typing import Any

from .blackboard import LemmaBlackboard
from .capabilities import CapabilityService
from .curriculum import CurriculumCase
from .distillation import VerifiedDistiller
from .executor import MechanicalExecutor
from .experience import ExperienceStore
from .obligations import ObligationGraph
from .planner import Planner
from .protocol import EpisodeRecord, ExecutionResult, StrategyArtifact
from .semantics import SemanticService
from .verifier import OfficialLeanVerifier


def _compact_action(action: dict[str, Any] | None) -> dict[str, Any] | None:
    if action is None:
        return None
    out = dict(action)
    for key in ("code", "proof"):
        value = out.get(key)
        if isinstance(value, str):
            out[key] = {
                "sha256": hashlib.sha256(value.encode("utf-8")).hexdigest(),
                "bytes": len(value.encode("utf-8")),
            }
    return out


def _bounded(value: Any, *, depth: int = 0) -> Any:
    """Bound feedback size without discarding its mathematical decision points."""
    if depth >= 6:
        return "<nested feedback omitted>"
    if isinstance(value, str):
        return value if len(value) <= 900 else value[:900] + "..."
    if isinstance(value, list):
        return [_bounded(item, depth=depth + 1) for item in value[:6]]
    if isinstance(value, dict):
        return {
            str(key): _bounded(item, depth=depth + 1)
            for key, item in list(value.items())[:24]
        }
    return value


def compact_mechanical_feedback(
    state: dict[str, Any] | None,
    *,
    execution_status: str | None = None,
    verification: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Translate a large worker state into one actionable System-2 observation."""
    source = state if isinstance(state, dict) else {}
    feedback: dict[str, Any] = {
        "kind": source.get("kind") or "MechanicalObservation",
        "status": execution_status or source.get("status") or "unknown",
    }
    for key in (
        "source",
        "need_hint",
        "suggested_next_actions",
        "recommended_next_action",
        "proved_lemmas",
        "failed_midpoints",
        "diagnostic_highlights",
        "untried_requested_routes",
        "tried_routes",
        "attempts",
        "budget_allocation",
    ):
        if source.get(key) not in (None, [], {}):
            feedback[key] = _bounded(source[key])

    search = source.get("goal_search_state") or source.get("search_state")
    if isinstance(search, dict):
        feedback["goal_search"] = _bounded({
            key: search.get(key)
            for key in (
                "status",
                "target",
                "need_hint",
                "closest_pairs",
                "suggested_next_actions",
                "failed_hints",
            )
            if search.get(key) not in (None, [], {})
        })
        superposition = search.get("superposition_state")
        if isinstance(superposition, dict):
            derived_structure = {
                key: superposition.get(key)
                for key in (
                    "target_shape",
                    "stop_reason",
                    "derived_closest_equations",
                    "shape_diagnostics",
                    "need_hint",
                )
                if superposition.get(key) not in (None, [], {})
            }
            rowconst = superposition.get("rowconst_diagnostics")
            if isinstance(rowconst, dict):
                derived_structure["auxiliary_shape_diagnostics"] = {
                    key: rowconst.get(key)
                    for key in (
                        "near_aux_shapes",
                        "recommended_next_action",
                        "rejected_recommendations",
                        "secondary_bridge_candidates",
                        "reason",
                    )
                    if rowconst.get(key) not in (None, [], {})
                }
            if derived_structure:
                feedback["derived_structure"] = _bounded(derived_structure)
    if verification is not None:
        feedback["verification"] = _bounded({
            key: verification.get(key)
            for key in ("status", "accepted", "verdict", "message", "error_code")
            if verification.get(key) is not None
        })
    return feedback


def _planner_trace(planner: Planner) -> dict[str, Any] | None:
    trace = getattr(planner, "last_trace", None)
    return _bounded(trace) if isinstance(trace, dict) else None


def _resume_observations(prior: dict[str, Any] | None) -> list[dict[str, Any]]:
    source = prior if isinstance(prior, dict) else {}
    metadata = source.get("metadata") if isinstance(source.get("metadata"), dict) else {}
    saved = metadata.get("final_recent_observations")
    if isinstance(saved, list):
        return [_bounded(row) for row in saved[-3:] if isinstance(row, dict)]
    observations: list[dict[str, Any]] = []
    for attempt in (source.get("attempts") or [])[-3:]:
        if not isinstance(attempt, dict):
            continue
        execution = attempt.get("execution")
        if isinstance(execution, dict):
            observations.append({
                "prior_round": attempt.get("round"),
                **compact_mechanical_feedback(
                    execution.get("state"),
                    execution_status=execution.get("status"),
                    verification=attempt.get("verification"),
                ),
            })
            continue
        preflight = attempt.get("blackboard_preflight")
        if isinstance(preflight, dict):
            observations.append({
                "prior_round": attempt.get("round"),
                "kind": "LemmaBlackboardObservation",
                "status": preflight.get("status"),
                "state": _bounded(preflight),
            })
    return observations[-3:]


class ResearchEpisodeRunner:
    def __init__(
        self,
        *,
        semantics: SemanticService,
        executor: MechanicalExecutor,
        verifier: OfficialLeanVerifier,
        store: ExperienceStore | None = None,
        distiller: VerifiedDistiller | None = None,
        capabilities: CapabilityService | None = None,
        retrieval_limit: int = 0,
    ):
        self.semantics = semantics
        self.executor = executor
        self.verifier = verifier
        self.store = store
        self.distiller = distiller
        self.capabilities = capabilities or CapabilityService()
        self.retrieval_limit = max(0, int(retrieval_limit))

    def run(
        self,
        case: CurriculumCase,
        planner: Planner,
        *,
        resume_from: dict[str, Any] | None = None,
    ) -> tuple[EpisodeRecord, StrategyArtifact | None]:
        started = time.monotonic()
        semantic = self.semantics.classify(case.problem)
        prior = resume_from if isinstance(resume_from, dict) else None
        blackboard = LemmaBlackboard.from_verified_snapshot(
            prior.get("blackboard") if prior else None
        )
        obligation_graph = ObligationGraph.from_snapshot(
            prior.get("obligations") if prior else None
        )
        recent_observations = _resume_observations(prior)
        capability_manifest = self.capabilities.manifest(case.capability_mask)
        def retrieve_for_current_state() -> list[dict[str, Any]]:
            if self.store is None or self.retrieval_limit <= 0:
                return []
            return self.store.retrieve_artifacts(
                semantic_class=semantic.semantic_class,
                problem=case.problem,
                capability_mask=case.capability_mask,
                blackboard=blackboard.snapshot(),
                limit=self.retrieval_limit,
            )

        retrieved_artifacts = retrieve_for_current_state()
        episode = EpisodeRecord(
            episode_id=f"episode_{uuid.uuid4().hex}",
            case_id=case.case_id,
            problem=case.problem.to_mapping(),
            semantics=semantic.to_mapping(),
            capability_mask=case.capability_mask,
            planner=planner.name,
            split_label=case.split_label,
            started_at=datetime.now(timezone.utc).isoformat(),
            metadata={
                "tags": list(case.tags),
                "expected_verdict": case.expected_verdict,
                "verification_profile": case.verification_profile,
                "retrieval": {
                    "limit": self.retrieval_limit,
                    "artifact_ids": [row.get("artifact_id") for row in retrieved_artifacts],
                },
                "resume": {
                    "parent_episode_id": prior.get("episode_id") if prior else None,
                    "trusted_node_count": len(blackboard.trusted_nodes),
                    "refuted_node_count": len(blackboard.refuted_nodes),
                    "observation_count": len(recent_observations),
                    "obligation_node_count": len(obligation_graph.nodes),
                },
                "components": {
                    "executor": self.executor.name,
                    "verifier": type(self.verifier).__name__,
                    "distiller": self.distiller.name if self.distiller else None,
                },
                "budget_policy": getattr(self.executor, "budget_policy", None),
            },
        )
        last_execution: ExecutionResult | None = None

        for round_index in range(1, case.max_rounds + 1):
            retrieved_artifacts = retrieve_for_current_state()
            automatic_action, automatic_state = obligation_graph.materialize_unattempted(
                blackboard=blackboard.snapshot(),
                round_index=round_index,
            )
            if automatic_action is not None:
                raw_action = {
                    "kind": "obligation_graph_continue",
                    "source": "automatic_dependency_scheduler",
                }
                prepared_action = automatic_action
                obligation_preflight = automatic_state
                planner_trace = {
                    "status": "action_ready",
                    "source": "automatic_dependency_scheduler",
                    "selected_nodes": automatic_state.get("selected_nodes"),
                }
            else:
                context = {
                    "problem": case.problem.to_mapping(),
                    "semantics": semantic.to_mapping(),
                    "capability_mask": case.capability_mask,
                    "blackboard": blackboard.snapshot(),
                    "obligation_graph": obligation_graph.planner_view(),
                    "recent_observations": recent_observations[-3:],
                    "round": round_index,
                    "rounds_remaining": case.max_rounds - round_index + 1,
                    "capability_manifest": capability_manifest,
                    "retrieved_artifacts": _bounded(retrieved_artifacts),
                }
                raw_action = planner.next_action(context)
                planner_trace = _planner_trace(planner)
                if raw_action is None:
                    if planner_trace is not None:
                        episode.attempts.append({
                            "round": round_index,
                            "raw_action": None,
                            "planner_trace": planner_trace,
                            "obligation_graph": obligation_graph.snapshot(),
                            "status": "planner_no_action",
                        })
                    episode.outcome = (
                        "planner_failed"
                        if planner_trace and planner_trace.get("status") in {
                            "configuration_error", "provider_error", "parse_error"
                        }
                        else "planner_exhausted"
                    )
                    break
                prepared_action, obligation_preflight = obligation_graph.prepare_action(
                    raw_action,
                    blackboard=blackboard.snapshot(),
                    round_index=round_index,
                )
                if prepared_action is None:
                    episode.attempts.append({
                        "round": round_index,
                        "raw_action": _compact_action(raw_action),
                        "planner_trace": planner_trace,
                        "obligation_preflight": obligation_preflight,
                        "status": obligation_preflight.get("status"),
                    })
                    recent_observations.append({
                        "round": round_index,
                        "kind": "ObligationGraphObservation",
                        "status": obligation_preflight.get("status"),
                        "state": _bounded(obligation_preflight),
                    })
                    continue

            normalized, adapter_state = self.executor.normalize(prepared_action)
            if normalized is None:
                attempt = {
                    "round": round_index,
                    "raw_action": _compact_action(raw_action),
                    "planner_trace": planner_trace,
                    "prepared_action": _compact_action(prepared_action),
                    "obligation_preflight": obligation_preflight,
                    "normalized_action": None,
                    "adapter_state": adapter_state,
                    "status": "adapter_rejected",
                }
                episode.attempts.append(attempt)
                recent_observations.append({
                    "round": round_index,
                    "kind": "LLMAdapterObservation",
                    "status": "adapter_rejected",
                    "adapter_state": _bounded(adapter_state),
                })
                continue

            submitted, preflight = blackboard.materialize_action(
                normalized,
                round_index=round_index,
            )
            if submitted is None:
                attempt = {
                    "round": round_index,
                    "raw_action": _compact_action(raw_action),
                    "planner_trace": planner_trace,
                    "prepared_action": _compact_action(prepared_action),
                    "obligation_preflight": obligation_preflight,
                    "normalized_action": _compact_action(normalized),
                    "submitted_action": None,
                    "blackboard_preflight": preflight,
                    "status": preflight.get("status"),
                }
                episode.attempts.append(attempt)
                recent_observations.append({
                    "round": round_index,
                    "kind": "LemmaBlackboardObservation",
                    "status": preflight.get("status"),
                    "state": _bounded(preflight),
                })
                continue

            execution = self.executor.execute(
                case.problem,
                submitted,
                capability_mask=case.capability_mask,
                semantics=semantic,
                action_is_normalized=True,
                adapter_state=adapter_state,
            )
            last_execution = execution
            update = blackboard.absorb_mechanical_state(
                submitted,
                execution.state,
                round_index=round_index,
            )
            verification = None
            if execution.has_candidate:
                verification = self.verifier.verify(
                    case.problem,
                    execution,
                    profile=case.verification_profile,
                )
            obligation_update = obligation_graph.absorb_mechanical_state(
                submitted,
                execution.state,
                round_index=round_index,
                accepted=bool(verification and verification.accepted),
            )
            attempt = {
                "round": round_index,
                "raw_action": _compact_action(raw_action),
                "planner_trace": planner_trace,
                "prepared_action": _compact_action(prepared_action),
                "obligation_preflight": obligation_preflight,
                "normalized_action": _compact_action(normalized),
                "submitted_action": _compact_action(submitted),
                "adapter_state": adapter_state,
                "blackboard_preflight": preflight,
                "blackboard_update": update,
                "obligation_update": obligation_update,
                "execution": execution.to_mapping(),
                "verification": verification.to_mapping() if verification else None,
                "status": "accepted" if verification and verification.accepted else execution.status,
            }
            episode.attempts.append(attempt)
            recent_observations.append({
                "round": round_index,
                **compact_mechanical_feedback(
                    execution.state,
                    execution_status=execution.status,
                    verification=verification.to_mapping() if verification else None,
                ),
            })
            if verification and verification.accepted:
                episode.accepted = True
                episode.verification = verification.to_mapping()
                episode.outcome = f"accepted_{verification.verdict}"
                break
        else:
            episode.outcome = "round_limit_exhausted"

        episode.blackboard = blackboard.snapshot()
        episode.obligations = obligation_graph.snapshot()
        episode.metadata["final_recent_observations"] = recent_observations[-3:]
        episode.metadata["retrieval"]["final_artifact_ids"] = [
            row.get("artifact_id") for row in retrieved_artifacts
        ]
        episode.metadata["retrieval"]["final_scores"] = [
            (row.get("_retrieval") or {}).get("score")
            for row in retrieved_artifacts
            if isinstance(row, dict)
        ]
        episode.seconds = round(time.monotonic() - started, 3)
        if self.store is not None:
            self.store.append_episode(episode)
        artifact = self.distiller.distill(episode, last_execution) if self.distiller else None
        if artifact is not None and self.store is not None:
            self.store.append_artifact(artifact)
        return episode, artifact
