"""Verified bounded-beam teacher search and ordinary-budget student replay."""

from __future__ import annotations

import hashlib
import json
import random
import time
import uuid
from concurrent.futures import ThreadPoolExecutor
from copy import deepcopy
from dataclasses import asdict, dataclass
from dataclasses import replace as dataclass_replace
from typing import Any, Callable

from .curriculum import CurriculumCase
from .orchestrator import ResearchEpisodeRunner
from .planner import Planner, ScriptedPlanner
from .protocol import EpisodeRecord, StrategyArtifact
from .structure import problem_structure
from .infinite_models import is_infinite_model_patch, merge_infinite_model_patch


TEACHER_STUDENT_VERSION = "sair-teacher-student-v1"
StudentPlannerFactory = Callable[[dict[str, Any] | None], Planner]
TeacherPlannerFactory = Callable[[], Planner]


def action_signature(action: dict[str, Any]) -> str:
    encoded = json.dumps(action, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def compact_action(action: dict[str, Any]) -> dict[str, Any]:
    out = deepcopy(action)
    for key in ("code", "proof"):
        value = out.get(key)
        if isinstance(value, str):
            out[key] = {
                "sha256": hashlib.sha256(value.encode("utf-8")).hexdigest(),
                "bytes": len(value.encode("utf-8")),
            }
    return out


@dataclass(frozen=True)
class TeacherSearchConfig:
    beam_width: int = 3
    proposals_per_branch: int = 4
    max_depth: int = 4
    branch_rounds: int = 2
    exploration_fraction: float = 0.25
    student_rounds: int = 4
    run_no_lesson_counterfactual: bool = True
    focus: str = "auto"
    proposal_workers: int = 4
    size_probe_max: int = 4
    seed: int = 0

    def normalized(self) -> "TeacherSearchConfig":
        focus = str(self.focus or "auto").strip().lower()
        if focus not in {"auto", "general", "finite_symbolic", "infinite_model"}:
            focus = "auto"
        return TeacherSearchConfig(
            beam_width=max(1, min(16, int(self.beam_width))),
            proposals_per_branch=max(1, min(16, int(self.proposals_per_branch))),
            max_depth=max(1, min(12, int(self.max_depth))),
            branch_rounds=max(1, min(8, int(self.branch_rounds))),
            exploration_fraction=max(0.0, min(0.75, float(self.exploration_fraction))),
            student_rounds=max(1, min(12, int(self.student_rounds))),
            run_no_lesson_counterfactual=bool(self.run_no_lesson_counterfactual),
            focus=focus,
            proposal_workers=max(1, min(16, int(self.proposal_workers))),
            size_probe_max=max(2, min(5, int(self.size_probe_max))),
            seed=int(self.seed),
        )


@dataclass
class BeamBranch:
    branch_id: str
    parent_id: str | None
    depth: int
    actions: list[dict[str, Any]]
    action: dict[str, Any]
    action_signature: str
    episode: EpisodeRecord
    score: float
    score_breakdown: dict[str, float]
    planner_trace: dict[str, Any] | None = None

    def to_mapping(self) -> dict[str, Any]:
        return {
            "branch_id": self.branch_id,
            "parent_id": self.parent_id,
            "depth": self.depth,
            "actions": [compact_action(action) for action in self.actions],
            "action": compact_action(self.action),
            "action_signature": self.action_signature,
            "episode_id": self.episode.episode_id,
            "accepted": self.episode.accepted,
            "outcome": self.episode.outcome,
            "score": self.score,
            "score_breakdown": self.score_breakdown,
            "planner_trace": self.planner_trace,
        }

    def to_resume_mapping(self) -> dict[str, Any]:
        return {
            "branch_id": self.branch_id,
            "parent_id": self.parent_id,
            "depth": self.depth,
            "actions": deepcopy(self.actions),
            "action": deepcopy(self.action),
            "action_signature": self.action_signature,
            "episode": self.episode.to_mapping(),
            "score": self.score,
            "score_breakdown": deepcopy(self.score_breakdown),
            "planner_trace": deepcopy(self.planner_trace),
        }

    @classmethod
    def from_resume_mapping(cls, data: dict[str, Any]) -> "BeamBranch":
        return cls(
            branch_id=str(data["branch_id"]),
            parent_id=str(data["parent_id"]) if data.get("parent_id") else None,
            depth=int(data.get("depth") or 0),
            actions=[dict(action) for action in data.get("actions") or []],
            action=dict(data.get("action") or {}),
            action_signature=str(data.get("action_signature") or ""),
            episode=EpisodeRecord.from_mapping(dict(data.get("episode") or {})),
            score=float(data.get("score") or 0.0),
            score_breakdown={
                str(key): float(value)
                for key, value in (data.get("score_breakdown") or {}).items()
            },
            planner_trace=(
                dict(data["planner_trace"])
                if isinstance(data.get("planner_trace"), dict)
                else None
            ),
        )


def _latest_execution_state(episode: EpisodeRecord) -> tuple[str | None, dict[str, Any]]:
    for attempt in reversed(episode.attempts):
        if not isinstance(attempt, dict):
            continue
        execution = attempt.get("execution")
        if not isinstance(execution, dict):
            continue
        state = execution.get("state")
        return str(execution.get("status") or ""), state if isinstance(state, dict) else {}
    return None, {}


def score_episode(episode: EpisodeRecord, *, depth: int) -> tuple[float, dict[str, float]]:
    """Rank only mechanically observed progress, never LLM confidence."""
    status, state = _latest_execution_state(episode)
    trusted = len(episode.blackboard.get("trusted_nodes") or [])
    proved_obligations = sum(
        1
        for node in episode.obligations.get("nodes") or []
        if isinstance(node, dict) and node.get("status") == "proved"
    )
    breakdown: dict[str, float] = {
        "accepted": 1_000_000.0 if episode.accepted else 0.0,
        "trusted_lemmas": 500.0 * trusted,
        "proved_obligations": 200.0 * proved_obligations,
        "depth_cost": -5.0 * depth,
    }
    if status == "candidate_ready":
        breakdown["candidate_ready"] = 100.0
    if state.get("need_hint"):
        breakdown["actionable_feedback"] = 20.0
    if state.get("suggested_next_actions") or state.get("recommended_next_action"):
        breakdown["continuation_available"] = 25.0
    if state.get("kind") == "InfiniteModelPlanState":
        breakdown["structured_parts"] = 100.0 * int(state.get("part_count") or 0)
        for attempt in reversed(episode.attempts):
            verification = attempt.get("verification") if isinstance(attempt, dict) else None
            details = verification.get("details") if isinstance(verification, dict) else None
            if (
                isinstance(verification, dict)
                and (
                    verification.get("message")
                    or (isinstance(details, dict) and details.get("stderr"))
                )
            ):
                breakdown["lean_repair_diagnostic"] = 50.0
                break
    if state.get("kind") == "SkewProductSearchState":
        if state.get("status") == "family_infeasible":
            breakdown["skew_family_eliminated"] = 40.0
        elif state.get("status") == "search_incomplete":
            breakdown["skew_partial_search"] = 180.0
        if state.get("last_goal_witness") or state.get("goal_witness"):
            breakdown["skew_goal_separation"] = 80.0
    if state.get("kind") == "BundleModelSearchState":
        if state.get("status") == "family_infeasible":
            breakdown["bundle_family_eliminated"] = 40.0
        elif state.get("status") == "search_incomplete":
            breakdown["bundle_partial_search"] = 180.0
        parameters = state.get("parameters")
        if isinstance(parameters, dict):
            breakdown["bundle_verified_parameters"] = 240.0
            breakdown["bundle_sparse_patches"] = max(
                0.0,
                80.0 - 5.0 * float(parameters.get("patch_count") or 0),
            )

    repair_class = str(state.get("repair_class") or "")
    h_profile = state.get("h_profile") if isinstance(state.get("h_profile"), dict) else {}
    g_profile = state.get("g_profile") if isinstance(state.get("g_profile"), dict) else {}
    h_failures = int(h_profile.get("failures_observed") or 0)
    h_checked = max(1, int(h_profile.get("assignments_checked") or 1))
    g_failures = int(g_profile.get("failures_observed") or 0)
    if repair_class == "verified_countermodel":
        breakdown["family_repair_class"] = 20_000.0
    elif repair_class == "repair_h_preserve_g":
        breakdown["family_repair_class"] = 650.0
        breakdown["family_h_proximity"] = max(
            0.0,
            400.0 * (1.0 - min(1.0, h_failures / h_checked)),
        )
        breakdown["family_goal_break"] = 80.0 if g_failures > 0 else 0.0
    elif repair_class == "break_g_preserve_h":
        breakdown["family_repair_class"] = 500.0
    elif repair_class == "target_goal_break":
        breakdown["family_repair_class"] = 300.0
    elif repair_class == "reduce_or_symbolically_justify":
        breakdown["family_repair_class"] = 100.0

    false_diagnostics = state.get("diagnostic_highlights")
    if isinstance(false_diagnostics, dict):
        best = false_diagnostics.get("best_partial_table")
        if isinstance(best, dict):
            h_violations = int(best.get("h_violations") or best.get("violations") or 0)
            breakdown["partial_table"] = max(0.0, 180.0 - 4.0 * h_violations)

    score = round(sum(breakdown.values()), 6)
    return score, breakdown


class TeacherStudentSearch:
    """Spend extra planner calls while holding each mechanical action contract fixed."""

    def __init__(
        self,
        runner: ResearchEpisodeRunner,
        teacher_planner: Planner,
        *,
        config: TeacherSearchConfig | None = None,
        student_planner_factory: StudentPlannerFactory | None = None,
        teacher_planner_factory: TeacherPlannerFactory | None = None,
    ):
        self.runner = runner
        self.teacher_planner = teacher_planner
        self.config = (config or TeacherSearchConfig()).normalized()
        self.student_planner_factory = student_planner_factory
        self.teacher_planner_factory = teacher_planner_factory
        self._rng = random.Random(self.config.seed)

    def _mechanical_diagnostics(self, case: CurriculumCase, semantic: Any) -> dict[str, Any]:
        provider = getattr(self.runner.executor, "planner_diagnostics", None)
        if not callable(provider):
            return {}
        try:
            value = provider(
                case.problem,
                semantics=semantic,
                max_carrier=self.config.size_probe_max,
            )
        except Exception as exc:
            return {"status": "diagnostics_failed", "error": repr(exc)}
        return value if isinstance(value, dict) else {}

    def _context(
        self,
        case: CurriculumCase,
        *,
        semantic: Any,
        parent: BeamBranch | None,
        depth: int,
        proposal_index: int,
        avoided: list[dict[str, Any]],
        diagnostics: dict[str, Any],
    ) -> dict[str, Any]:
        prior = parent.episode if parent is not None else None
        metadata = prior.metadata if prior is not None else {}
        recent = metadata.get("final_recent_observations")
        focus = self.config.focus
        if focus == "auto":
            if (
                case.expected_verdict == "false"
                and diagnostics.get("finite_countermodel_search_allowed") is False
            ):
                focus = "infinite_model"
            elif case.expected_verdict == "false":
                focus = "finite_symbolic"
            else:
                focus = "general"
        if focus == "finite_symbolic":
            directive = (
                "Return kind=false_model_family, kind=skew_model_search, or "
                "kind=bundle_model_search only. Do not "
                "call fixed-route false_model_search or true-side proof tools. Use "
                "false_model_family for a coherent compact operation formula and repair "
                "its H-violating regions while preserving a concrete G failure. Use "
                "skew_model_search when a small quotient with block-dependent fibers may "
                "compress a larger table; after family_infeasible feedback, change factor "
                "sizes or the fiber library rather than resubmitting it. Use "
                "bundle_model_search with unequal fiber_sizes and a gradually increased "
                "max_patches when equal fibers are too rigid; the mechanical side "
                "enumerates quotient laws and fills all affine maps and exceptions. "
                "Cell conditions use "
                '{"kind":"cell","i":0,"j":1}; machine feedback includes exact examples '
                "and hot cells. Respect mechanical_diagnostics.minimum_unexcluded_carrier_size; "
                "do not repair a carrier already proved unable to contain a countermodel."
            )
        elif focus == "infinite_model":
            directive = (
                "Finite countermodels are unavailable for this lane. Prefer a structured "
                "symbolic_model_plan with representation=infinite, carrier, optional "
                "pre-model definitions, operation, setup lemmas, hypothesis_proof, and "
                "counterexample_proof. Use the supplied "
                "construction-family cards to select a representation. After a rejected "
                "parent plan, return symbolic_model_patch changing only failed_parts; preserve "
                "preserve_parts and use exact Lean stderr. A complete kind=infinite_model "
                "artifact remains an expert fast path."
            )
        else:
            directive = (
                "Propose a materially different action from the avoided candidates. "
                "Use mechanical near-miss feedback from the parent branch."
            )
        return {
            "problem": case.problem.to_mapping(),
            "semantics": semantic.to_mapping(),
            "capability_mask": case.capability_mask,
            "capability_manifest": self.runner.capabilities.manifest(case.capability_mask),
            "blackboard": deepcopy(prior.blackboard) if prior is not None else {},
            "obligation_graph": deepcopy(prior.obligations) if prior is not None else {},
            "recent_observations": deepcopy(recent) if isinstance(recent, list) else [],
            "retrieved_artifacts": [],
            "round": depth,
            "rounds_remaining": self.config.max_depth - depth + 1,
            "mechanical_diagnostics": deepcopy(diagnostics),
            "teacher_search": {
                "version": TEACHER_STUDENT_VERSION,
                "mode": "bounded_beam_teacher",
                "depth": depth,
                "proposal_index": proposal_index,
                "proposals_at_this_parent": self.config.proposals_per_branch,
                "beam_width": self.config.beam_width,
                "focus": focus,
                "avoid_actions": deepcopy(avoided[-12:]),
                "parent_action": compact_action(parent.action) if parent is not None else None,
                "parent_action_lineage": (
                    [compact_action(action) for action in parent.actions[-3:]]
                    if parent is not None
                    else []
                ),
                "directive": directive,
            },
        }

    def _propose_one(
        self,
        context: dict[str, Any],
    ) -> tuple[dict[str, Any] | None, dict[str, Any] | None]:
        planner = (
            self.teacher_planner_factory()
            if self.teacher_planner_factory is not None
            else self.teacher_planner
        )
        action = planner.next_action(context)
        trace = getattr(planner, "last_trace", None)
        return (
            action,
            deepcopy(trace) if isinstance(trace, dict) else None,
        )

    def _propose_batch(
        self,
        requests: list[tuple[BeamBranch | None, int, dict[str, Any]]],
    ) -> list[tuple[BeamBranch | None, int, dict[str, Any] | None, dict[str, Any] | None]]:
        if self.teacher_planner_factory is None or len(requests) <= 1:
            return [
                (parent, proposal_index, *self._propose_one(context))
                for parent, proposal_index, context in requests
            ]
        with ThreadPoolExecutor(
            max_workers=min(self.config.proposal_workers, len(requests)),
            thread_name_prefix="sair-teacher",
        ) as pool:
            futures = [
                pool.submit(self._propose_one, context)
                for _parent, _proposal_index, context in requests
            ]
            results = [future.result() for future in futures]
        return [
            (parent, proposal_index, action, trace)
            for (parent, proposal_index, _context), (action, trace)
            in zip(requests, results)
        ]

    def _record_episode(self, episode: EpisodeRecord, metadata: dict[str, Any]) -> None:
        episode.metadata["teacher_student"] = deepcopy(metadata)
        if self.runner.store is not None:
            self.runner.store.append_episode(episode)

    def _execute_branch(
        self,
        case: CurriculumCase,
        action: dict[str, Any],
        *,
        parent: BeamBranch | None,
        depth: int,
        planner_trace: dict[str, Any] | None,
    ) -> BeamBranch:
        branch_case = dataclass_replace(
            case,
            max_rounds=self.config.branch_rounds,
        )
        episode, _ = self.runner.run(
            branch_case,
            ScriptedPlanner([action], name="teacher_candidate"),
            resume_from=parent.episode.to_mapping() if parent is not None else None,
            persist=False,
            distill=False,
        )
        signature = action_signature(action)
        score, breakdown = score_episode(episode, depth=depth)
        branch = BeamBranch(
            branch_id=f"branch_{uuid.uuid4().hex[:12]}",
            parent_id=parent.branch_id if parent is not None else None,
            depth=depth,
            actions=(list(parent.actions) if parent is not None else []) + [deepcopy(action)],
            action=deepcopy(action),
            action_signature=signature,
            episode=episode,
            score=score,
            score_breakdown=breakdown,
            planner_trace=deepcopy(planner_trace),
        )
        self._record_episode(episode, {
            "version": TEACHER_STUDENT_VERSION,
            "role": "teacher_branch",
            "branch_id": branch.branch_id,
            "parent_id": branch.parent_id,
            "depth": depth,
            "score": score,
            "action_signature": signature,
        })
        return branch

    def _select_beam(self, candidates: list[BeamBranch]) -> list[BeamBranch]:
        ordered = sorted(
            candidates,
            key=lambda branch: (-branch.score, branch.depth, branch.action_signature),
        )
        width = min(self.config.beam_width, len(ordered))
        if width <= 1:
            return ordered[:width]
        exploration_slots = 0
        if self.config.exploration_fraction > 0:
            exploration_slots = min(
                width - 1,
                max(1, int(round(width * self.config.exploration_fraction))),
            )
        exploitation_slots = width - exploration_slots
        selected = ordered[:exploitation_slots]
        remainder = ordered[exploitation_slots:]
        while exploration_slots and remainder:
            represented = {
                str(branch.action.get("kind") or branch.action.get("tool") or "unknown")
                for branch in selected
            }
            diverse = [
                branch
                for branch in remainder
                if str(
                    branch.action.get("kind")
                    or branch.action.get("tool")
                    or "unknown"
                )
                not in represented
            ]
            pool = diverse or remainder
            choice = self._rng.choice(pool)
            selected.append(choice)
            remainder.remove(choice)
            exploration_slots -= 1
        return selected

    def _replay(
        self,
        case: CurriculumCase,
        actions: list[dict[str, Any]],
        *,
        role: str,
    ) -> EpisodeRecord:
        replay_case = dataclass_replace(
            case,
            max_rounds=max(
                self.config.student_rounds,
                len(actions) * self.config.branch_rounds + 1,
            ),
        )
        episode, _ = self.runner.run(
            replay_case,
            ScriptedPlanner(deepcopy(actions), name=role),
            persist=False,
            distill=False,
        )
        self._record_episode(episode, {
            "version": TEACHER_STUDENT_VERSION,
            "role": role,
            "action_count": len(actions),
        })
        return episode

    def _minimize(
        self,
        case: CurriculumCase,
        actions: list[dict[str, Any]],
    ) -> tuple[list[dict[str, Any]], EpisodeRecord, list[dict[str, Any]]]:
        current = deepcopy(actions)
        trials: list[dict[str, Any]] = []
        baseline = self._replay(case, current, role="teacher_mechanical_replay")
        if not baseline.accepted:
            return current, baseline, trials
        index = 0
        while len(current) > 1 and index < len(current):
            candidate = current[:index] + current[index + 1 :]
            trial = self._replay(case, candidate, role="teacher_minimization_trial")
            trials.append({
                "removed_index": index,
                "accepted": trial.accepted,
                "outcome": trial.outcome,
                "remaining_action_count": len(candidate),
            })
            if trial.accepted:
                current = candidate
                baseline = trial
                index = 0
            else:
                index += 1
        return current, baseline, trials

    def _student_run(
        self,
        case: CurriculumCase,
        lesson: dict[str, Any] | None,
        *,
        role: str,
    ) -> EpisodeRecord | None:
        if self.student_planner_factory is None:
            return None
        planner = self.student_planner_factory(deepcopy(lesson))
        student_case = dataclass_replace(case, max_rounds=self.config.student_rounds)
        episode, _ = self.runner.run(
            student_case,
            planner,
            persist=False,
            distill=False,
        )
        self._record_episode(episode, {
            "version": TEACHER_STUDENT_VERSION,
            "role": role,
            "lesson_present": lesson is not None,
        })
        return episode

    def replay_student_lesson(
        self,
        case: CurriculumCase,
        lesson: dict[str, Any],
    ) -> dict[str, Any]:
        """Run an ordinary-budget attribution pair for one verified lesson."""
        counterfactual = None
        if (
            self.student_planner_factory is not None
            and self.config.run_no_lesson_counterfactual
        ):
            counterfactual = self._student_run(
                case,
                None,
                role="student_no_lesson_counterfactual",
            )
        student = self._student_run(
            case,
            lesson,
            role="student_with_lesson",
        )
        student_ok = bool(student and self._expected(student, case))
        counterfactual_ok = bool(
            counterfactual and self._expected(counterfactual, case)
        )
        return {
            "no_lesson": counterfactual,
            "with_lesson": student,
            "student_accepted": student_ok,
            "no_lesson_accepted": counterfactual_ok,
            "load_bearing": bool(student_ok and not counterfactual_ok),
        }

    @staticmethod
    def _expected(episode: EpisodeRecord, case: CurriculumCase) -> bool:
        return bool(
            episode.accepted
            and (episode.verification or {}).get("verdict") == case.expected_verdict
        )

    def _lesson(
        self,
        case: CurriculumCase,
        winner: BeamBranch,
        minimized_actions: list[dict[str, Any]],
    ) -> dict[str, Any]:
        _status, final_state = _latest_execution_state(winner.episode)
        return {
            "version": TEACHER_STUDENT_VERSION,
            "kind": "verified_teacher_trajectory",
            "problem_structure": problem_structure(case.problem),
            "expected_verdict": case.expected_verdict,
            "decisive_actions": deepcopy(minimized_actions),
            "teacher_depth": winner.depth,
            "teacher_score": winner.score,
            "final_mechanical_feedback": deepcopy(final_state),
            "instruction": (
                "Adapt the decisive action to the current problem and state. "
                "The mechanical verifier must independently accept it."
            ),
        }

    def _artifact(
        self,
        case: CurriculumCase,
        lesson: dict[str, Any],
        winner: BeamBranch,
        student: EpisodeRecord,
        counterfactual: EpisodeRecord | None,
    ) -> StrategyArtifact:
        identity = {
            "case_id": case.case_id,
            "lesson": lesson,
            "student_episode": student.episode_id,
        }
        digest = hashlib.sha256(
            json.dumps(identity, sort_keys=True).encode("utf-8")
        ).hexdigest()[:16]
        return StrategyArtifact(
            artifact_id=f"teacher_lesson_{digest}",
            kind="teacher_student_lesson",
            status="verified",
            deployability="research_candidate",
            trigger={
                "problem_structure": problem_structure(case.problem),
                "semantic_class": winner.episode.semantics.get("semantic_class"),
                "capability_context": case.capability_mask,
            },
            payload={
                "version": TEACHER_STUDENT_VERSION,
                "lesson": lesson,
                "attribution": {
                    "teacher_episode_id": winner.episode.episode_id,
                    "student_episode_id": student.episode_id,
                    "no_lesson_episode_id": (
                        counterfactual.episode_id if counterfactual is not None else None
                    ),
                    "no_lesson_accepted": bool(counterfactual and counterfactual.accepted),
                    "lesson_accepted": student.accepted,
                },
            },
            evidence={
                "case_id": case.case_id,
                "verification": student.verification,
            },
        )

    def run(
        self,
        case: CurriculumCase,
        *,
        resume_from: dict[str, Any] | None = None,
    ) -> dict[str, Any]:
        started = time.monotonic()
        semantic = self.runner.semantics.classify(case.problem)
        diagnostics = self._mechanical_diagnostics(case, semantic)
        resume = (
            resume_from.get("resume_state")
            if isinstance(resume_from, dict)
            and isinstance(resume_from.get("resume_state"), dict)
            else None
        )
        if resume and resume.get("case_id") != case.case_id:
            raise ValueError(
                f"teacher resume case mismatch: {resume.get('case_id')} != {case.case_id}"
            )
        resumed_beam = [
            BeamBranch.from_resume_mapping(row)
            for row in (resume or {}).get("beam") or []
            if isinstance(row, dict)
        ]
        beam: list[BeamBranch | None] = resumed_beam or [None]
        generations: list[dict[str, Any]] = [
            dict(row)
            for row in (resume or {}).get("generations") or []
            if isinstance(row, dict)
        ]
        winners: list[BeamBranch] = []
        seen_actions: dict[str, dict[str, Any]] = {
            str(signature): dict(action)
            for signature, action in ((resume or {}).get("seen_actions") or {}).items()
            if isinstance(action, dict)
        }
        seen: set[str] = set(seen_actions)
        provider_failures = int((resume or {}).get("provider_failure_count") or 0)
        policy_rejections = int((resume or {}).get("policy_rejection_count") or 0)
        start_depth = (
            max((branch.depth for branch in resumed_beam), default=0) + 1
            if resumed_beam
            else 1
        )

        for depth in range(start_depth, self.config.max_depth + 1):
            candidates: list[BeamBranch] = []
            rejected_duplicates = 0
            generation_policy_rejections = 0
            proposal_requests: list[
                tuple[BeamBranch | None, int, dict[str, Any]]
            ] = []
            for parent in beam:
                avoided = [
                    seen_actions[signature]
                    for signature in sorted(seen_actions)
                ]
                for proposal_index in range(1, self.config.proposals_per_branch + 1):
                    context = self._context(
                        case,
                        semantic=semantic,
                        parent=parent,
                        depth=depth,
                        proposal_index=proposal_index,
                        avoided=avoided,
                        diagnostics=diagnostics,
                    )
                    proposal_requests.append((parent, proposal_index, context))
            for parent, _proposal_index, action, trace in self._propose_batch(proposal_requests):
                if action is None:
                    provider_failures += 1
                    continue
                if is_infinite_model_patch(action) and parent is not None:
                    action = merge_infinite_model_patch(parent.action, action)
                source = action.get("family") if isinstance(action.get("family"), dict) else action
                action_kind = str(
                    action.get("tool")
                    if action.get("kind") == "tool_call"
                    else action.get("kind")
                    or ""
                )
                try:
                    proposed_n = int(source.get("carrier_size") or source.get("n") or 0)
                    if not proposed_n and action_kind == "skew_model_search":
                        proposed_n = int(source.get("control_size") or 0) * int(
                            source.get("fiber_size") or 0
                        )
                    if not proposed_n and action_kind == "bundle_model_search":
                        fibers = source.get("fiber_sizes") or source.get("block_sizes") or []
                        if isinstance(fibers, (list, tuple)):
                            proposed_n = sum(int(value) for value in fibers)
                except Exception:
                    proposed_n = 0
                minimum_n = int(diagnostics.get("minimum_unexcluded_carrier_size") or 0)
                if (
                    minimum_n
                    and proposed_n
                    and proposed_n < minimum_n
                    and (
                        action.get("kind") == "false_model_family"
                        or action.get("tool") == "false_model_family"
                        or action_kind == "skew_model_search"
                        or action_kind == "bundle_model_search"
                    )
                ):
                    policy_rejections += 1
                    generation_policy_rejections += 1
                    continue
                signature = action_signature(action)
                if signature in seen:
                    rejected_duplicates += 1
                    continue
                seen.add(signature)
                seen_actions[signature] = compact_action(action)
                branch = self._execute_branch(
                    case,
                    action,
                    parent=parent,
                    depth=depth,
                    planner_trace=trace,
                )
                candidates.append(branch)
                if self._expected(branch.episode, case):
                    winners.append(branch)
            selected = self._select_beam(candidates)
            generations.append({
                "depth": depth,
                "candidate_count": len(candidates),
                "duplicate_count": rejected_duplicates,
                "policy_rejection_count": generation_policy_rejections,
                "selected_branch_ids": [branch.branch_id for branch in selected],
                "candidates": [branch.to_mapping() for branch in candidates],
            })
            if winners:
                break
            if not selected:
                break
            beam = selected

        if not winners:
            return {
                "version": TEACHER_STUDENT_VERSION,
                "case_id": case.case_id,
                "outcome": "teacher_unsolved",
                "teacher": {
                    "planner": self.teacher_planner.name,
                    "config": asdict(self.config),
                    "generations": generations,
                    "unique_action_count": len(seen),
                    "provider_failure_count": provider_failures,
                    "policy_rejection_count": policy_rejections,
                },
                "resume_state": {
                    "version": TEACHER_STUDENT_VERSION,
                    "case_id": case.case_id,
                    "next_depth": (
                        max((branch.depth for branch in beam if branch is not None), default=0)
                        + 1
                    ),
                    "beam": [
                        branch.to_resume_mapping()
                        for branch in beam
                        if branch is not None
                    ],
                    "seen_actions": deepcopy(seen_actions),
                    "provider_failure_count": provider_failures,
                    "policy_rejection_count": policy_rejections,
                    "generations": generations,
                },
                "mechanical_diagnostics": diagnostics,
                "seconds": round(time.monotonic() - started, 3),
            }

        winner = sorted(
            winners,
            key=lambda branch: (branch.depth, -branch.score, branch.action_signature),
        )[0]
        minimized, mechanical_replay, minimization_trials = self._minimize(
            case,
            winner.actions,
        )
        lesson = self._lesson(case, winner, minimized)
        replay = self.replay_student_lesson(case, lesson)
        counterfactual = replay["no_lesson"]
        student = replay["with_lesson"]
        mechanical_replay_ok = self._expected(mechanical_replay, case)
        student_ok = bool(replay["student_accepted"])
        counterfactual_ok = bool(replay["no_lesson_accepted"])

        artifact = None
        if not mechanical_replay_ok or not student_ok:
            outcome = "teacher_solved_not_distillable"
        elif counterfactual is None:
            outcome = "student_replay_unattributed"
        elif counterfactual_ok:
            outcome = "student_replay_non_attributable"
        else:
            outcome = "student_replay"
            assert student is not None
            artifact = self._artifact(
                case,
                lesson,
                winner,
                student,
                counterfactual,
            )
            if self.runner.store is not None:
                self.runner.store.append_artifact(artifact)

        return {
            "version": TEACHER_STUDENT_VERSION,
            "case_id": case.case_id,
            "outcome": outcome,
            "teacher": {
                "planner": self.teacher_planner.name,
                "config": asdict(self.config),
                "generations": generations,
                "unique_action_count": len(seen),
                "provider_failure_count": provider_failures,
                "policy_rejection_count": policy_rejections,
                "winner": winner.to_mapping(),
            },
            "minimization": {
                "original_action_count": len(winner.actions),
                "minimized_action_count": len(minimized),
                "actions": [compact_action(action) for action in minimized],
                "mechanical_replay_episode": mechanical_replay.to_mapping(),
                "trials": minimization_trials,
            },
            "student": {
                "no_lesson": counterfactual.to_mapping() if counterfactual else None,
                "with_lesson": student.to_mapping() if student else None,
                "load_bearing": bool(student_ok and not counterfactual_ok),
            },
            "artifact": artifact.to_mapping() if artifact else None,
            "resume_state": None,
            "mechanical_diagnostics": diagnostics,
            "seconds": round(time.monotonic() - started, 3),
        }
