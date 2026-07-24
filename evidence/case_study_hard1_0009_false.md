# Case Study: `hard1_0009` False-Side Route Selection

This case illustrates the false-side collaboration path: mechanical proof
search fails, false-route telemetry asks for a concrete continuation, and the
LLM selects a finite-model search route that the mechanical side verifies.

## Problem

```text
H    : x = (((x ◇ x) ◇ (y ◇ z)) ◇ y)
Goal : x = (((x ◇ (y ◇ x)) ◇ x) ◇ y)
```

## Mechanical Feedback

The initial equality graph did not connect the target:

```json
{
  "status": "direct_goal_not_connected",
  "target": "x = (((x ◇ (y ◇ x)) ◇ x) ◇ y)",
  "left_component_size": 11,
  "right_component_size": 31,
  "facts_generated": 920
}
```

A later true-side Lean attempt also failed with a `grind` error. The false-side
feedback then gave a compact instruction:

```json
{
  "kind": "false_route_collaboration_state",
  "status": "native_v2_false_search_failed",
  "need_hint": "Select one untried false_model_search continuation from the telemetry; do not repeat tried routes."
}
```

## LLM Proposal

The live model selected a concrete local-search continuation:

```json
{
  "kind": "tool_call",
  "tool": "false_model_search",
  "target": "goal",
  "template": "local_search",
  "routes": ["local_search:n=6:seed=2"],
  "budget": 6
}
```

## Mechanical Consumption

The mechanical side ran that route, found a six-element countermodel, rendered a
Lean certificate, and the official judge accepted it:

```lean
let m : Magma (Fin 6) := {
  op := finOpTable "[[2, 2, 2, 2, 2, 2], [3, 5, 1, 5, 5, 5], [4, 4, 4, 4, 4, 4], [1, 1, 5, 1, 3, 1], [0, 0, 0, 0, 0, 0], [5, 3, 3, 3, 1, 3]]"
}
refine ⟨Fin 6, m, ?_⟩
decideFin!
```

The accepted judge attempt was attributed to
`llm:false_model_search:table`. See:

- machine-readable summary: `cases/hard1_0009_false_model_search.json`
- Lean certificate: `lean/hard1_0009_countermodel.lean`
