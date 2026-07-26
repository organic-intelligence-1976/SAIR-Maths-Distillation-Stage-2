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
            "Do not call an unavailable tool. Prefer a reusable universal helper over restating the goal with its variables.",
            "Closest-pair equations are diagnostics, not commands: generalize their recurring algebraic shape before proposing a helper.",
            "When several genuinely different mechanisms are plausible, use one proof_plan with family-labeled nodes. Dependencies are AND prerequisites; alternative_group marks OR routes.",
            "Allowed JSON shapes include:",
            '{"kind":"proof_plan","nodes":[{"id":"collapse","equation":"a ◇ b = c ◇ d","family_id":"operation_collapse","mechanism":"derive global product collapse","alternative_group":"root_bridge","depends_on":[],"advances":"root"},{"id":"projection","equation":"a ◇ b = a","family_id":"projection","mechanism":"derive a projection law","alternative_group":"root_bridge","depends_on":[],"advances":"root"}]}',
            '{"kind":"midpoint","lemma":"<new universal helper equation>"}',
            '{"kind":"tool_call","tool":"lemma_chain","target":"goal","lemmas":[{"name":"helper","equation":"<new universal helper equation>"}]}',
            '{"kind":"tool_call","tool":"goal_superposition","target":"goal","budget":8}',
            '{"kind":"tool_call","tool":"false_model_search","target":"goal","routes":["model_finder_v2:n=6"],"budget":8}',
            '{"kind":"false_model_family","carrier_size":8,"default":{"kind":"affine","params":[1,0,0]},"rules":[{"when":{"kind":"diagonal"},"value":"i+1"}],"budget":8}',
            '{"kind":"false_table","counterexample_table":[[0,1],[1,0]]}',
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
