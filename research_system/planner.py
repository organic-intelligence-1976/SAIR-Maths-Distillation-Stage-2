"""System-2 planner interfaces with scripted and OpenAI-compatible implementations."""

from __future__ import annotations

import json
import os
import hashlib
import urllib.error
import urllib.request
from copy import deepcopy
from typing import Any, Callable, Protocol

from .structure import canonical_equation_signature, dual_equation


class Planner(Protocol):
    name: str

    def next_action(self, context: dict[str, Any]) -> dict[str, Any] | None: ...


class ScriptedPlanner:
    """Deterministic planner used for contract tests and known rediscoveries."""

    def __init__(self, actions: list[dict[str, Any]], name: str = "scripted"):
        self.name = name
        self._actions = [deepcopy(action) for action in actions]
        self._index = 0

    def next_action(self, context: dict[str, Any]) -> dict[str, Any] | None:
        del context
        if self._index >= len(self._actions):
            return None
        action = deepcopy(self._actions[self._index])
        self._index += 1
        return action


class FunctionPlanner:
    """Adapter for experiments that provide their own planning callable."""

    def __init__(self, function: Callable[[dict[str, Any]], dict[str, Any] | None], name: str = "function"):
        self.function = function
        self.name = name

    def next_action(self, context: dict[str, Any]) -> dict[str, Any] | None:
        return self.function(context)


class ContextAugmentingPlanner:
    """Add research-only context without changing the wrapped planner contract."""

    def __init__(
        self,
        planner: Planner,
        additions: dict[str, Any],
        *,
        name: str | None = None,
    ):
        self.planner = planner
        self.additions = deepcopy(additions)
        self.name = name or f"context:{planner.name}"

    @property
    def last_trace(self) -> dict[str, Any] | None:
        trace = getattr(self.planner, "last_trace", None)
        return deepcopy(trace) if isinstance(trace, dict) else None

    def next_action(self, context: dict[str, Any]) -> dict[str, Any] | None:
        augmented = deepcopy(context)
        augmented.update(deepcopy(self.additions))
        return self.planner.next_action(augmented)


def _matches_recommended_action(
    action: dict[str, Any] | None,
    recommended: dict[str, Any],
) -> bool:
    if not isinstance(action, dict):
        return False
    kind = str(action.get("kind") or "").strip().lower()
    if kind == "tool_call":
        kind = str(action.get("tool") or "").strip().lower()
    expected_kind = str(recommended.get("kind") or "").strip().lower()
    if expected_kind == "tool_call":
        expected_kind = str(recommended.get("tool") or "").strip().lower()
    aliases = {
        "fiber_bundle_search": "bundle_model_search",
        "patched_bundle_search": "bundle_model_search",
        "skew_product_search": "skew_model_search",
        "block_model_search": "skew_model_search",
    }
    kind = aliases.get(kind, kind)
    expected_kind = aliases.get(expected_kind, expected_kind)
    if kind != expected_kind:
        return False
    if expected_kind == "bundle_model_search":
        actual_fibers = action.get("fiber_sizes") or action.get("block_sizes")
        expected_fibers = (
            recommended.get("fiber_sizes") or recommended.get("block_sizes")
        )
        return (
            list(actual_fibers or []) == list(expected_fibers or [])
            and int(action.get("max_patches") or 0)
            == int(recommended.get("max_patches") or 0)
        )
    if expected_kind == "skew_model_search":
        return (
            int(action.get("control_size") or action.get("quotient_size") or 0)
            == int(
                recommended.get("control_size")
                or recommended.get("quotient_size")
                or 0
            )
            and int(action.get("fiber_size") or 0)
            == int(recommended.get("fiber_size") or 0)
        )
    return action == recommended


class FeedbackRepairPlanner:
    """Give System 2 one bounded correction when it ignores exact feedback."""

    def __init__(
        self,
        planner: Planner,
        *,
        max_corrections: int = 1,
        name: str | None = None,
    ):
        self.planner = planner
        self.max_corrections = max(0, min(3, int(max_corrections)))
        self.name = name or f"feedback_repair:{planner.name}"
        self.last_trace: dict[str, Any] | None = None

    def next_action(self, context: dict[str, Any]) -> dict[str, Any] | None:
        action = self.planner.next_action(context)
        traces = []
        trace = getattr(self.planner, "last_trace", None)
        if isinstance(trace, dict):
            traces.append(deepcopy(trace))
        observations = context.get("recent_observations")
        latest = (
            observations[-1]
            if isinstance(observations, list)
            and observations
            and isinstance(observations[-1], dict)
            else {}
        )
        suggestions = latest.get("suggested_next_actions")
        recommended = (
            suggestions[0]
            if isinstance(suggestions, list)
            and suggestions
            and isinstance(suggestions[0], dict)
            else None
        )
        corrections = 0
        while (
            corrections < self.max_corrections
            and latest.get("mechanical_status") == "family_infeasible"
            and recommended is not None
            and not _matches_recommended_action(action, recommended)
        ):
            corrections += 1
            repaired_context = deepcopy(context)
            repaired_observations = list(
                repaired_context.get("recent_observations") or []
            )
            repaired_observations.append({
                "kind": "LLMAdapterState",
                "status": "correction_required",
                "mechanical_status": "family_infeasible",
                "error_code": "ignored_primary_mechanical_repair",
                "rejected_action": action,
                "required_action": recommended,
                "need_hint": (
                    "Return required_action exactly. The previous compact model "
                    "configuration was mechanically proved infeasible."
                ),
            })
            repaired_context["recent_observations"] = repaired_observations[-3:]
            action = self.planner.next_action(repaired_context)
            trace = getattr(self.planner, "last_trace", None)
            if isinstance(trace, dict):
                traces.append(deepcopy(trace))
        self.last_trace = {
            "status": "action_ready" if action is not None else "no_action",
            "source": "feedback_repair_planner",
            "correction_count": corrections,
            "matched_primary_recommendation": bool(
                recommended is not None
                and _matches_recommended_action(action, recommended)
            ),
            "delegate_traces": traces,
        }
        return action


class RetrievedLessonPlanner:
    """Deterministic baseline that replays only missing nodes from the best lesson.

    This is not a trusted shortcut: target-side mechanics must prove every
    retrieved universal equation again and the final body still goes to Lean.
    """

    def __init__(self, name: str = "retrieved_verified_lesson_v1"):
        self.name = name
        self.last_trace: dict[str, Any] | None = None

    def next_action(self, context: dict[str, Any]) -> dict[str, Any] | None:
        artifacts = context.get("retrieved_artifacts") or []
        for artifact in artifacts:
            if not isinstance(artifact, dict) or artifact.get("status") != "verified":
                continue
            if artifact.get("kind") != "proof_plan_schema":
                continue
            payload = artifact.get("payload") if isinstance(artifact.get("payload"), dict) else {}
            nodes = payload.get("plan_nodes") if isinstance(payload.get("plan_nodes"), list) else []
            retrieval = artifact.get("_retrieval") if isinstance(artifact.get("_retrieval"), dict) else {}
            has_missing_metadata = "missing_plan_node_signatures" in retrieval
            missing = set(str(item) for item in retrieval.get("missing_plan_node_signatures") or [])
            transform = retrieval.get("plan_transform")
            lemmas = []
            for node in nodes:
                if not isinstance(node, dict) or not isinstance(node.get("equation"), str):
                    continue
                equation = str(node["equation"])
                name = node.get("name") or node.get("node_id")
                if transform == "magma_dual":
                    equation = dual_equation(equation)
                    name = f"{name}_dual"
                signature = canonical_equation_signature(equation)
                if has_missing_metadata and signature not in missing:
                    continue
                lemmas.append({"name": name, "equation": equation})
            if not lemmas:
                continue
            self.last_trace = {
                "status": "action_ready",
                "source": "verified_structural_retrieval",
                "artifact_id": artifact.get("artifact_id"),
                "retrieval_score": retrieval.get("score"),
                "retrieval_reasons": retrieval.get("reasons"),
                "selected_node_count": len(lemmas),
                "plan_transform": transform or "identity",
            }
            return {
                "kind": "tool_call",
                "tool": "lemma_chain",
                "target": "goal",
                "lemmas": lemmas,
                "why": "replay missing nodes from the highest-scoring mechanically verified structural lesson",
            }
        self.last_trace = {
            "status": "no_structurally_compatible_verified_lesson",
            "source": "verified_structural_retrieval",
            "retrieved_count": len(artifacts),
        }
        return None


class OpenAICompatiblePlanner:
    """Minimal live LLM planner with no trust over returned mathematics."""

    def __init__(
        self,
        config: dict[str, Any],
        *,
        prompt_builder: Callable[[dict[str, Any]], str] | None = None,
        timeout: float = 90.0,
    ):
        llm = config.get("llm") if isinstance(config.get("llm"), dict) else config
        self.config = dict(llm or {})
        self.timeout = timeout
        self.prompt_builder = prompt_builder or self.default_prompt
        self.name = f"llm:{self.config.get('model', 'openai/gpt-oss-120b')}"
        self.last_response: dict[str, Any] | None = None
        self.last_trace: dict[str, Any] | None = None

    @staticmethod
    def default_prompt(context: dict[str, Any]) -> str:
        manifest = context.get("capability_manifest")
        tools = manifest.get("tools") if isinstance(manifest, dict) else []
        available_tools = [
            {
                "tool": row.get("tool"),
                "domain": row.get("domain"),
                "description": row.get("description"),
            }
            for row in tools or []
            if isinstance(row, dict) and row.get("available")
        ]
        unavailable_tools = [
            str(row.get("tool"))
            for row in tools or []
            if isinstance(row, dict) and not row.get("available")
        ]
        compact = {
            "problem": context.get("problem"),
            "semantics": context.get("semantics"),
            "round": context.get("round"),
            "rounds_remaining": context.get("rounds_remaining"),
            "capability_mask": context.get("capability_mask"),
            "available_tools": available_tools,
            "unavailable_tools": unavailable_tools,
            "blackboard": context.get("blackboard"),
            "obligation_graph": context.get("obligation_graph"),
            "recent_observations": context.get("recent_observations"),
            "retrieved_verified_artifacts": context.get("retrieved_artifacts") or [],
            "mechanical_diagnostics": context.get("mechanical_diagnostics") or {},
            "teacher_search": context.get("teacher_search") or {},
            "teacher_lesson": context.get("teacher_lesson"),
        }
        return "\n".join([
            "You are the untrusted System-2 planner in a mechanically verified equational prover.",
            "Choose one useful mathematical next action. Do not explain your reasoning outside the JSON object.",
            "The mechanical side independently proves lemmas, validates tables, and verifies final artifacts in Lean.",
            "Trusted blackboard lemmas are retained and automatically prepended, so propose only missing unresolved nodes.",
            "Never repeat a refuted equation under renamed variables or reversed equality.",
            "If a lemma was proved but the goal remained stuck, extend the partial plan instead of replacing that lemma.",
            "Retrieved lessons are structurally matched verified experience, not trusted target proofs. Reuse only their missing plan nodes; the target mechanics will prove them again.",
            "The obligation graph tracks approach families, dependencies, blocked routes, and evidence. Advance an open obligation; do not rename a blocked mechanism and resubmit it.",
            "A blocked exact node may be reopened only with reopen_novelty describing a materially new construction, invariant, representation, or proof mechanism.",
            "When the latest observation has mechanical_status=family_infeasible and suggested_next_actions, use the first suggested action exactly unless you can identify a concrete structural reason to choose another. Never repeat the rejected configuration unchanged.",
            "Do not call an unavailable tool. Prefer a reusable universal helper over restating the goal with its variables.",
            "Closest-pair equations are diagnostics, not commands: generalize their recurring algebraic shape before proposing a helper.",
            "During teacher search, use the proposal slot and avoided-action list to explore a genuinely different mathematical family, not a renamed duplicate.",
            "Obey teacher_search.directive exactly; it defines which action language this experiment is evaluating.",
            "When teacher_search.parent_action is present, return a complete repaired replacement for that exact action unless the feedback justifies changing family or carrier.",
            "Never use a carrier below mechanical_diagnostics.minimum_unexcluded_carrier_size; those sizes were exhaustively eliminated by the mechanical side.",
            "A teacher lesson is verified experience, not a trusted target proof. Adapt its decisive action to the current state; the mechanical side will check it again.",
            "For an exact-problem student replay, preserve a complete verified decisive action verbatim on the first attempt, including all mutually referenced Lean identifiers. Improvise only after mechanical feedback rejects that replay.",
            "When several genuinely different mechanisms are plausible, use one proof_plan with family-labeled nodes. Dependencies are AND prerequisites; alternative_group marks OR routes.",
            "Allowed JSON shapes include:",
            '{"kind":"proof_plan","nodes":[{"id":"collapse","equation":"a ◇ b = c ◇ d","family_id":"operation_collapse","mechanism":"derive global product collapse","alternative_group":"root_bridge","depends_on":[],"advances":"root"},{"id":"projection","equation":"a ◇ b = a","family_id":"projection","mechanism":"derive a projection law","alternative_group":"root_bridge","depends_on":[],"advances":"root"}]}',
            '{"kind":"midpoint","lemma":"<new universal helper equation>"}',
            '{"kind":"tool_call","tool":"lemma_chain","target":"goal","lemmas":[{"name":"helper","equation":"<new universal helper equation>"}]}',
            '{"kind":"tool_call","tool":"goal_superposition","target":"goal","budget":8}',
            '{"kind":"tool_call","tool":"false_model_search","target":"goal","routes":["model_finder_v2:n=6"],"budget":8}',
            '{"kind":"false_model_family","carrier_size":8,"default":{"kind":"affine","params":[1,0,0]},"rules":[{"when":{"kind":"diagonal"},"value":"i+1"}],"budget":8}',
            'false_model_family conditions: diagonal, off_diagonal, same_mod, different_mod, left_residue, right_residue, or {"kind":"cell","i":0,"j":1}; string conditions may use i, j, n and bounded arithmetic/comparisons.',
            '{"kind":"skew_model_search","control_size":2,"fiber_size":3,"fiber_library":"affine","require_quotient_goal":true,"budget":15}',
            "skew_model_search mechanically synthesizes a Q-by-fiber extension. With require_quotient_goal=true, the smaller quotient satisfies both H and G, so only block-dependent fiber maps may create the counterexample. Change factor sizes or the fiber library after family_infeasible feedback.",
            '{"kind":"bundle_model_search","fiber_sizes":[4,2],"fiber_library":"affine_patches","max_patches":6,"require_quotient_goal":true,"budget":30}',
            "bundle_model_search generalizes skew_model_search to unequal fibers. The mechanical side enumerates small quotient tables satisfying H and G, synthesizes affine maps between each pair of fibers, and permits at most max_patches exceptional cells. Use it when equal-factor searches fail or feedback suggests a non-uniform quotient; increase max_patches gradually.",
            "Finite bundle search heuristic: after an equal 2-by-k extension is mechanically infeasible, keep two quotient blocks but try unequal fibers and increase total carrier one step at a time, such as [k+1,k]. Start with sparse patches (roughly 10-20 percent of table cells), then increase only after an infeasibility certificate. This is a search policy, not evidence that any proposed shape is correct.",
            '{"kind":"false_table","counterexample_table":[[0,1],[1,0]]}',
            '{"kind":"infinite_model_plan","model_name":"model","imports":["Mathlib.Tactic"],"carrier":"ℕ","operation":"fun x y ↦ ...","setup":["have helper : ... := by\\n  ..."],"hypothesis_proof":"intro x y z\\n...","counterexample_proof":"simp only [not_forall]\\nuse ...\\n..."}',
            '{"kind":"infinite_model_patch","set":{"hypothesis_proof":"<complete repaired tactic body>"}}',
            "Angle-bracket text above is schema notation only; replace it with actual mathematics.",
            "Return exactly one JSON object and no markdown.",
            json.dumps(compact, ensure_ascii=False, sort_keys=True),
        ])

    def next_action(self, context: dict[str, Any]) -> dict[str, Any] | None:
        base_url = (
            self.config.get("base_url")
            or os.environ.get("OPENAI_BASE_URL")
            or "https://openrouter.ai/api/v1"
        ).rstrip("/")
        key_env = self.config.get("api_key_env")
        if key_env:
            api_key = os.environ.get(key_env, "")
        elif "openrouter.ai" in base_url:
            api_key = os.environ.get("OPENROUTER_API_KEY") or os.environ.get("OPENAI_API_KEY") or ""
        else:
            api_key = os.environ.get("OPENAI_API_KEY") or os.environ.get("OPENROUTER_API_KEY") or ""
        if not api_key:
            self.last_response = {"error": f"{key_env or 'OPENAI_API_KEY/OPENROUTER_API_KEY'} not set"}
            self.last_trace = {
                "status": "configuration_error",
                "error": self.last_response["error"],
            }
            return None
        prompt = self.prompt_builder(context)
        body: dict[str, Any] = {
            "model": self.config.get("model", "openai/gpt-oss-120b"),
            "messages": [
                {"role": "system", "content": "Return exactly one JSON object and no prose."},
                {"role": "user", "content": prompt},
            ],
            "temperature": float(self.config.get("temperature", 0.0)),
            "max_tokens": int(self.config.get("max_output_tokens", 1024)),
        }
        if self.config.get("use_seed"):
            body["seed"] = int(self.config.get("seed", 0))
        if "openrouter.ai" in base_url and self.config.get("provider"):
            body["provider"] = {"order": [self.config["provider"]]}
        if "openrouter.ai" in base_url and self.config.get("reasoning_effort"):
            body["reasoning"] = {"effort": self.config["reasoning_effort"]}
        request = urllib.request.Request(
            f"{base_url}/chat/completions",
            data=json.dumps(body).encode("utf-8"),
            headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
            method="POST",
        )
        self.last_trace = {
            "status": "request_started",
            "model": body["model"],
            "prompt_sha256": hashlib.sha256(prompt.encode("utf-8")).hexdigest(),
            "prompt_bytes": len(prompt.encode("utf-8")),
            "round": context.get("round"),
        }
        try:
            with urllib.request.urlopen(request, timeout=max(1.0, self.timeout)) as response:
                payload = json.loads(response.read().decode("utf-8"))
            text = str(payload["choices"][0]["message"]["content"])
            self.last_response = {"response": text, "usage": payload.get("usage")}
            self.last_trace.update({
                "status": "response_received",
                "response_bytes": len(text.encode("utf-8")),
                "usage": payload.get("usage"),
            })
        except urllib.error.HTTPError as exc:
            self.last_response = {"error": f"HTTP {exc.code}: {exc.read().decode('utf-8', 'replace')[:1000]}"}
            self.last_trace.update({"status": "provider_error", "error": self.last_response["error"]})
            return None
        except Exception as exc:
            self.last_response = {"error": repr(exc)}
            self.last_trace.update({"status": "provider_error", "error": self.last_response["error"]})
            return None
        try:
            action = json.loads(text)
        except json.JSONDecodeError:
            start, end = text.find("{"), text.rfind("}")
            if start < 0 or end <= start:
                self.last_trace.update({"status": "parse_error", "error": "no JSON object found"})
                return None
            try:
                action = json.loads(text[start : end + 1])
            except json.JSONDecodeError:
                self.last_trace.update({"status": "parse_error", "error": "invalid JSON object"})
                return None
        if not isinstance(action, dict):
            self.last_trace.update({"status": "parse_error", "error": "response JSON was not an object"})
            return None
        self.last_trace["status"] = "action_ready"
        return action
