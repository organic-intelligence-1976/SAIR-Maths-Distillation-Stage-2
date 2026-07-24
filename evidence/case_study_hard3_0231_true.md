# Case Study: `hard3_0231` True-Side Helper Chain

This case illustrates the intended collaboration pattern on a true implication:
the LLM proposes reusable helper equations, while the mechanical side proves and
stitches them into a Lean certificate.

## Problem

```text
H    : x = ((y ◇ x) ◇ y) ◇ (z ◇ z)
Goal : x = (y ◇ (x ◇ (y ◇ x))) ◇ x
```

## Mechanical Stuck State

The deliberately weakened first mechanical pass did not connect the goal
components:

```json
{
  "status": "artificial_frontier_stuck",
  "target": "x = ((y ◇ (x ◇ (y ◇ x))) ◇ x)",
  "need_hint": {
    "kind": "bridge_terms",
    "left_term": "x",
    "right_term": "((y ◇ (x ◇ (y ◇ x))) ◇ x)"
  },
  "left_component_size": 1,
  "right_component_size": 9
}
```

## LLM Proposal

The live model returned a `lemma_chain`:

```json
{
  "kind": "tool_call",
  "tool": "lemma_chain",
  "target": "goal",
  "lemmas": [
    {"name": "square_const", "equation": "u ◇ u = v ◇ v"},
    {"name": "right_id_square", "equation": "u ◇ (v ◇ v) = u"},
    {"name": "sandwich", "equation": "(v ◇ u) ◇ v = u"},
    {"name": "left_sandwich", "equation": "v ◇ (u ◇ v) = u"}
  ]
}
```

## Mechanical Consumption

The helper-chain consumer independently proved all four proposed universal
lemmas from `H`, then used them to close the target. The final Lean certificate
contains the helper proofs and the goal-specific calculation:

```lean
have sq_chain_1 : (x ◇ (y ◇ x)) = y := by
  exact left_sandwich y x
have sq_chain_2 : (y ◇ (x ◇ (y ◇ x))) = (x ◇ x) := by
  calc
    (y ◇ (x ◇ (y ◇ x))) = (y ◇ y) := congrArg (fun u => y ◇ u) sq_chain_1
    _ = (x ◇ x) := square_const y x
have sq_chain_3 : ((y ◇ (x ◇ (y ◇ x))) ◇ x) = x := by
  calc
    ((y ◇ (x ◇ (y ◇ x))) ◇ x) = ((x ◇ x) ◇ x) := congrArg (fun u => u ◇ x) sq_chain_2
    _ = x := sandwich x x
exact sq_chain_3.symm
```

The official judge accepted the full certificate with no axioms. See:

- machine-readable summary: `cases/hard3_0231_lemma_chain.json`
- Lean certificate: `lean/hard3_0231_submission.lean`
