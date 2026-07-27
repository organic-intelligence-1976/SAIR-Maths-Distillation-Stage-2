# Recursive Bundle Countermodel: `hard2_0125`

This case study records a finite false-side collaboration in which the
mechanical system supplied a sequence of increasingly expressive model
families and a live `gpt-oss-120b` planner selected the next family from the
feedback. The final six-element table was accepted by the official Stage 2
Lean judge.

## Problem

```text
H: x = ((x ◇ (y ◇ z)) ◇ z) ◇ x
G: x = ((x ◇ x) ◇ (y ◇ y)) ◇ x
verdict: false
```

This is an architectural case, not a new coverage claim. A broad CP-SAT search
had already found an ordinary six-element countermodel. The new result is a
compact constructive language and a verified feedback ladder that reaches such
a model without asking the LLM to write a 6-by-6 table.

## Why A Plain Product Was Insufficient

A direct product uses the same component operation independently in each
coordinate. It cannot create a target failure when every factor already
satisfies the target law. The useful generalization is a quotient bundle:

```text
(q, u) ◇ (r, v) = (q ⋆ r, phi[q,r](u,v))
```

The quotient operation controls which output block receives the result.
Different quotient cells may use different fiber maps. The implementation also
allows a bounded number of exceptions to an affine fiber map.

The earlier equal-fiber constructor searched only `Q × F`. Analysis of the
known six-element model found one nontrivial congruence, with block sizes
`[4, 2]` and quotient table:

```text
0 0
1 1
```

That explains why equal factorizations missed this structure.

## Verified Feedback Ladder

The probe deliberately seeded one inexpensive equal-fiber attempt. Every later
action came from the live LLM after receiving compact mechanical feedback.

1. `skew_model_search`, `2 × 2`: mechanically `family_infeasible`.
2. The feedback proposed unequal fibers `[3, 2]` with four sparse patches. The
   LLM selected it; mechanics proved that family infeasible.
3. The feedback then prioritized growing one fiber over adding more patches.
   The LLM selected `[4, 2]` with six patches.
4. CP-SAT synthesized the quotient, four affine fiber maps, six exceptions,
   and a goal-breaking assignment. Exhaustive evaluation checked `H`, then the
   official Lean judge accepted the ordinary finite table.

The successful table in this run was:

```text
0 1 0 0 1 0
0 1 2 3 1 3
3 1 2 3 0 3
3 1 2 3 1 3
5 5 5 5 4 5
5 5 5 5 4 5
```

The LLM did not invent the table entries. Its load-bearing role was to consume
the failed-family state and select the next decomposition. System 1 synthesized
and checked all mathematical parameters.

## Recursive Interpretation

This gives a limited but principled divide-and-conquer route. A congruence
partitions a large magma into quotient states and fibers. A chain of
congruences yields nested bundle descriptions. Sparse patches increase the
expressivity of each local fiber map while preserving the exact quotient.

This recursion is not universal: a finite magma with no nontrivial congruence
cannot be decomposed this way. Such a residual needs another compact language,
for example a small decision tree, circuit, or a more general constraint
program. The new congruence analyzer makes that boundary observable.

## Reproduce

With OR-Tools, the official judge environment, and an API key configured:

```bash
python3 scripts/bundle_model_probe.py \
  --problem-id hard2_0125 \
  --fiber-sizes 4,2 \
  --max-patches 6

python3 scripts/bundle_feedback_probe.py \
  --problem-id hard2_0125 \
  --rounds 3
```

The compact machine-readable record is
[`recursive_bundle_countermodel_2026_07_26.json`](recursive_bundle_countermodel_2026_07_26.json).
