# Case Study: `hard3_0202` Candidate Repair

This case shows why mechanical diagnostics and candidate persistence matter.
The useful LLM contribution was not its first guess. It arrived after two
failed directions and a mechanical superposition trace exposed a narrower
equation near the target.

## Problem

```text
H    : x = (x ◇ (y ◇ z)) ◇ (y ◇ w)
Goal : x ◇ y = x ◇ ((y ◇ z) ◇ x)
```

## Historical Repair Trajectory

The retained full-verification run made three successful LLM calls:

1. It selected a bounded false-model search. No countermodel was found.
2. It proposed the stronger row-constancy law `a ◇ b = a ◇ c`.
3. After the mechanical response, it proposed the narrower contraction law
   `a ◇ ((b ◇ c) ◇ d) = a ◇ b`.

The second proposal did not merely return `false`. Its proof-carrying
superposition attempt reported `time_budget` after 368 generated equations and
returned close equations of the forms:

```text
a ◇ ((b ◇ c) ◇ d) = a ◇ b
a ◇ b = a ◇ ((b ◇ c) ◇ d)
```

The third LLM call used that feedback and returned exactly this contraction
family. The mechanical side independently proved the universal lemma from `H`,
specialized it with `a=x, b=y, c=z, d=x`, rendered Lean, and obtained an
axiom-free acceptance from the official judge.

## New Robustness Probe

The candidate-blackboard implementation also accepts a substantially less
precise provider output. In a deterministic probe, the supplied candidate was
just the specialized goal itself:

```text
x ◇ y = x ◇ ((y ◇ z) ◇ x)
```

Repeating the goal is not a valid midpoint. The normalizer therefore tried a
small, bounded lattice of untrusted variants. Splitting the final repeated `x`
into a fresh variable produced:

```text
x ◇ y = x ◇ ((y ◇ z) ◇ a)
```

This is alpha-equivalent to the winning universal contraction law. The
mechanical consumer proved it and closed the goal in about 2.7 seconds. Other
generated variants were independently refuted or left budget-limited; none was
trusted because it looked plausible.

This expands the useful output basin without weakening soundness: normalization
only generates candidates, while the existing mechanical prover and Lean judge
remain responsible for every accepted statement.

## Persistent Status Vocabulary

Across later LLM rounds, each alpha/symmetry-normalized candidate now retains a
mechanically assigned status such as:

```text
counterexample_found
unproved_with_budget
proved_but_not_connected
second_leg_proved_first_leg_unproved
proved_and_helpful
```

The board also keeps separate diagnostics for `H => M` and `{H, M} => G`.
Mechanically proved but unused facts are reconsidered alongside new proposals;
refuted duplicates are blocked.

See the machine-readable summary in
`cases/hard3_0202_candidate_repair.json` and the accepted certificate in
`lean/hard3_0202_submission.lean`.
