# Mechanical / LLM Protocol v0

This document is the first rigorous version of the communication contract
between the trusted mechanical solver and the untrusted LLM strategist.

The goal is to let the two sides develop independently while keeping the outer
loop simple.

## Roles

**System 1: mechanical side**

- trusted proof and model machinery;
- owns Lean proof generation, countermodel checking, and all soundness;
- may import the reference mechanical baseline modules as tools;
- must report useful structured progress when it gets stuck.

**System 2: LLM side**

- untrusted strategist;
- proposes tool calls, midpoint lemmas, lemma chains, proof snippets, repair
  actions, or finite-model search routes;
- may be wrong, syntactically sloppy, or repetitive;
- never contributes trusted mathematical facts directly.

**Protocol adapter**

- normalizes LLM JSON into bounded mechanical requests;
- repairs obvious envelope mistakes, such as `tool_name` vs `tool`;
- rejects unsupported actions before they reach a tool;
- translates mechanical failures into compact LLM-readable feedback.

## Invariants

1. LLM mathematical content is never trusted.
2. Every accepted true result must be checked by Lean through the official
   judge.
3. Every accepted false result must be checked as a real countermodel.
4. The adapter may repair syntax and envelope mistakes, but not silently assume
   a nontrivial mathematical theorem.
5. Every serious mechanical failure should answer:

```text
What did you try?
What did you prove or generate?
Why did the request fail?
What would be useful next?
Which exact repeats should be avoided?
```

## Tiny Outer Loop

The long-term loop should be this small:

```text
state = initial_problem
for round in budget:
    response = mechanical.try(state)
    if response.status in {"proved", "found_model"}:
        return verified artifact

    action = llm.propose(response.state)
    normalized = adapter.normalize(action)
    if normalized.rejected:
        state = state + adapter error feedback
        continue

    state = adapter.apply(normalized, response.state)

return unsolved or fallback
```

Implementation may still have scheduling and fallback details, but those should
live below this protocol boundary.

## Protocol Metadata

Every protocol-aware feedback object should include:

```json
{
  "protocol_version": "sair-collab-protocol-v0",
  "kind": "SearchState | MechanicalResponse | LLMAdapterState | FalseModelSearchState | ...",
  "status": "proved | found | stuck | rejected | syntax_repaired | timeout | not_applicable",
  "source": "graph_search | false_model_search | goal_superposition | llm_adapter | ..."
}
```

Existing module-specific fields may remain. The important rule is that common
fields have stable meanings:

- `source`: module or adapter that produced this feedback;
- `artifact_source`: old/raw route or proof source when preserving legacy
  `source` content;
- `need_hint`: the shortest useful description of what System 2 should supply;
- `suggested_next_actions`: executable next JSON actions when possible;
- `errors`: normalized parse, provider, judge, or protocol errors;
- `attempt`: compact description of budgets, limits, seed terms, or routes;
- `tool_state`: nested module state when a tool call failed or partially
  succeeded.

## LLM Actions

### Tool Call

```json
{
  "kind": "tool_call",
  "tool": "goal_superposition",
  "target": "goal",
  "budget": 8
}
```

Tool calls are for named mechanical tools. The adapter normalizes known aliases.
Unsupported tools are rejected with `status: unsupported_tool`.

### Midpoint

```json
{
  "kind": "midpoint",
  "lemma": "a ◇ b = c ◇ d",
  "why": "connects opconst-like frontier"
}
```

The solver tries:

```text
prove([H], M)
prove([H, M], G)
```

The midpoint is discarded unless both legs are mechanically verified.

### Lemma Chain

```json
{
  "kind": "lemma_chain",
  "lemmas": [
    {"name": "square_const", "equation": "u ◇ u = v ◇ v"},
    {"name": "right_id_square", "equation": "u ◇ (v ◇ v) = u"}
  ]
}
```

The solver proves each lemma in order. Later lemmas may use earlier proved
lemmas. The goal proof may use all proved lemmas.

### False-Model Search

```json
{
  "kind": "tool_call",
  "tool": "false_model_search",
  "routes": ["model_finder:n=4", "local_search:n=6:seed=2"],
  "budget": 8
}
```

Accepted route templates include:

- `local_search:n=6:seed=2`;
- `model_finder:n=4`;
- `model_finder_v2:n=6`;
- `cp_sat:n=6`;
- `poly_ce:tier=2:nmax=13`;
- `reference_ce:max_n=3`.

The adapter also accepts natural false hints such as:

```json
{"kind": "false_model_hint", "template": "local_search", "sizes": [6], "seeds": [2]}
```

and normalizes them to `false_model_search`.

False-search failures should report concrete `trials`, `untried_requested_routes`,
and `recommended_next_call`. The scheduler treats these as route memory across
LLM rounds and across the pre-child/final fallback boundary: repeated routes are
filtered, CP-SAT `UNKNOWN` routes can request larger budgets, and off-phase
generic true-side hints may be repaired to the top false continuation when the
false telemetry is more concrete.

### Direct Artifacts

Direct Lean proof bodies and counterexample tables are allowed but discouraged:

```json
{"kind": "goal_proof", "proof": "intro x y\n..."}
{"kind": "false_table", "counterexample_table": [[0, 1], [1, 0]]}
```

They are accepted only if the official judge verifies them.

## Adapter Repairs

The adapter may perform shallow repairs and must report them as
`LLMAdapterState`.

Current v0 repairs:

- `tool_name` -> `tool`;
- `kind: "tool"` -> `kind: "tool_call"`;
- `proof_body` -> `proof`;
- known tool aliases -> canonical tool names;
- false-model hints -> `false_model_search`;
- missing hint kind -> inferred `midpoint` or `midpoint_chain`.

Example:

```json
{
  "protocol_version": "sair-collab-protocol-v0",
  "kind": "LLMAdapterState",
  "status": "syntax_repaired",
  "source": "llm_adapter",
  "repairs": [
    {"code": "field_alias", "field": "tool_name", "message": "Renamed tool_name to tool"}
  ]
}
```

These repairs are intentionally syntactic. They do not make a mathematical
claim true.

## Mechanical Responses

### Proved

```json
{
  "protocol_version": "sair-collab-protocol-v0",
  "kind": "MechanicalResponse",
  "status": "proved",
  "source": "right_square_chain",
  "tool": "right_square_chain"
}
```

The proof body itself may stay outside the feedback if it is immediately sent
to the judge.

### Stuck Graph Search

```json
{
  "protocol_version": "sair-collab-protocol-v0",
  "kind": "SearchState",
  "status": "stuck",
  "source": "graph_search",
  "target": "x = y ◇ z",
  "facts_generated": 480,
  "left_component_size": 42,
  "right_component_size": 19,
  "closest_pairs": [
    {"left": "x ◇ y", "right": "z ◇ z", "similarity": 0.61}
  ],
  "need_hint": {
    "kind": "bridge_terms",
    "left_term": "x ◇ y",
    "right_term": "z ◇ z",
    "reason": "would connect the target equality components"
  },
  "suggested_next_actions": [
    {"kind": "midpoint", "lemma": "x ◇ y = z ◇ z"}
  ]
}
```

### False Search Miss

```json
{
  "protocol_version": "sair-collab-protocol-v0",
  "kind": "FalseModelSearchState",
  "status": "no_countermodel_found",
  "source": "false_model_search",
  "trials": [
    {"route": "model_finder_v2:n=5", "status": "none"}
  ],
  "diagnostic_highlights": {
    "tried_routes": ["model_finder_v2:n=5"],
    "status_counts": {"none": 1},
    "hot_blocked_cells": [{"cell": [1, 4], "count": 13789}],
    "hot_branch_cells": [{"cell": [1, 0], "count": 127}],
    "best_partial_progress": {
      "route": "model_finder_v2:n=5",
      "assigned_ratio": 0.92
    },
    "next_action_policy": [
      "Try recommended_next_call first; it is the first untried concrete route.",
      "Do not repeat exhausted routes; change route family, carrier size, seed, or provide a full table."
    ]
  },
  "untried_requested_routes": ["local_search:n=6:seed=2"],
  "recommended_next_call": {
    "kind": "tool_call",
    "tool": "false_model_search",
    "routes": ["local_search:n=6:seed=2"],
    "budget": 6
  }
}
```

## Status Codes

Recommended v0 statuses:

- `proved`: true proof body was produced;
- `found`: countermodel was produced;
- `body_built`: proof body was built but may not yet have been judged;
- `stuck`: search was meaningful but did not close;
- `not_applicable`: focused tool did not match this shape;
- `no_countermodel_found`: finite-model route failed under current budget;
- `parse_failed`: adapter could not parse an LLM response;
- `syntax_repaired`: adapter repaired a shallow envelope issue;
- `rejected`: adapter rejected an unsupported action;
- `duplicate_failed_call`: scheduler suppressed a repeated failed request;
- `judge_rejected_true_body`: Lean rejected a direct proof body;
- `timeout`: module exhausted its budget.

## Current Implementation Checkpoint

`baby_solver.py` now contains:

- `PROTOCOL_VERSION = "sair-collab-protocol-v0"`;
- `ProtocolIssue`;
- `protocol_state()`;
- `protocolize_state()`;
- `normalize_llm_action()`;
- protocol metadata on graph `SearchState`;
- protocol metadata on false-model search states;
- `diagnostic_highlights` on false-search misses, including tried routes, status
  counts, hot blocked/branch cells, best partial-table progress, and a compact
  next-action policy;
- protocol metadata on generic midpoint-chain attempts;
- tool feedback from `run_tool_call_detailed()` normalized into protocol-aware
  states;
- LLM collaboration loop normalization before acting on LLM JSON.

The implementation is deliberately incremental. The solver still has an older
scheduler and family-specific routes, but new modules can now target the v0
contract without waiting for a full rewrite.

Verification artifacts from the first implementation pass:

- `.artifacts/protocol_v0_hard3_0183_smoke.json`: packed solver accepted a true
  case after protocol metadata was added.
- `.artifacts/protocol_v0_hard2_0016_smoke.json`: packed solver accepted a false
  case after false-search states were protocolized.
- `.artifacts/protocol_feedback_highlights_smoke.json`: packed solver still
  accepted the true/false smoke after false-search miss highlights were added.
- `.artifacts/feedback_uptake_hard2_0125_v1.json`: lightweight live
  `gpt-oss-120b` uptake probe followed the false-search
  `recommended_next_call` from `diagnostic_highlights` and did not repeat the
  tried route.
- `.artifacts/feedback_uptake_hard2_0125_memory_none_v2.json`,
  `.artifacts/feedback_uptake_hard2_0125_memory_stale_v2.json`, and
  `.artifacts/feedback_uptake_hard2_0125_memory_exhaust_v2.json`: live uptake
  probes for clean, stale, and exhausted route-memory states. The model followed
  the fresh recommendation, moved to the next route when the first route was
  marked stale, and chose a supported untried action when no recommendation was
  left.
- `.artifacts/feedback_uptake_hard2_0027_memory_stale_v1.json` and
  `.artifacts/feedback_uptake_hard2_0027_memory_exhaust_v2.json`: same route-
  memory uptake on the hard false frontier. The exhausted state exposed useful
  adapter work: reject invented tools such as `true_midpoint`, reject goal-as-
  midpoint instantly in the generic midpoint consumer, and repair common JSON
  variants (`action` envelope, `type`/`kind` false-search alias, singular
  `route`). The repaired follow-up is preserved in
  `.artifacts/feedback_uptake_hard2_0027_goal_midpoint_repair_v3_reprocessed.json`.

## Next Implementation Steps

1. Move the top-level scheduler toward the tiny outer loop while preserving
   existing accepted routes.
2. Add a small attribution runner that labels each accepted case as:
   native mechanical, LLM-selected tool, LLM midpoint/chain, false route, or
   reference child fallback.
3. Convert more reference mechanical imports from wrapped tools to structured tools by
   returning `need_hint`, `closest_pairs`, and `suggested_next_actions`.
4. Add regression transcripts for:
   - one true midpoint repair;
   - one false-route repair;
   - one syntax-repaired LLM action.

The first syntax-repair transcript now exists:
`.artifacts/feedback_uptake_hard2_0027_goal_midpoint_repair_v3_reprocessed.json`.
It normalizes `{"action":{"kind":"false_model_search","route":"model_finder_v2:n=8"}}`
to a supported `false_model_search` tool call without treating the LLM output
as trusted mathematics.
