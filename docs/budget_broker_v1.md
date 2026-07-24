# Renewable Budget Broker v1

Status: working minimal implementation, 2026-07-18

The midpoint worker now treats every helper `M` as two separate obligations:

```text
attain:   H       -> M
consume:  H + M   -> Goal
```

The consume leg may run speculatively before attain succeeds. Its proof body is
not returned unless attain also succeeds. Final soundness is unchanged: every
returned body declares a mechanically proved `M` before any code that uses it,
and the official Lean verifier remains the acceptance boundary.

## Allocation rule

`RenewableBudgetBroker` gives every runnable task one initial grant before any
task gets a renewal. Failed tasks remain eligible for geometrically larger
grants up to a per-task cap. Whenever a new helper is proved, the proof context
version advances and exhausted legs may apply once in the stronger context.

The current transparent score is:

```text
base leg priority
+ goal relevance weight * static relevance
+ reuse weight * known reusable helper shape
+ exploration weight / sqrt(1 + grant count)
+ progress weight * coarse mechanical progress
+ companion-success bonus
- failure penalty * failed grants
+ deterministic seeded tie break
```

This is an intentionally replaceable value estimator, not a claim that the
weights are optimal. Budget is conservatively charged by the requested worker
seconds. Actual elapsed time is recorded separately in every report event.

## Genotype

The canonical starting policy is
`data/budget_policies/balanced_v1.json`. Its free parameters include the shared
budget, initial and maximum grants, geometric growth, grant cap, leg priorities,
scoring weights, and random seed. Values are bounded at the worker boundary so
malformed or extreme experiment files cannot create unbounded requests.

Run a reference suite under one genotype:

```bash
python3 scripts/run_research_episode.py \
  --budget-policy data/budget_policies/balanced_v1.json \
  --output .artifacts/budget_runs/balanced.json
```

Generate reproducible mutations:

```bash
python3 scripts/mutate_budget_policy.py \
  --output-dir .artifacts/budget_policies/generation_1 \
  --count 8 --seed 100
```

After running the same predeclared suite for each policy, rank the reports:

```bash
python3 scripts/budget_policy_scoreboard.py \
  .artifacts/budget_runs/*.json \
  --output .artifacts/budget_runs/scoreboard.json
```

Ranking is lexicographic: verified accepted cases first, then total episode
time, then committed broker budget. Held-out families and repeated seeds are
still required before calling a policy better; the scoreboard is selection
machinery, not statistical evidence by itself.

## Current limitations

- A grant controls the bounded superposition portion of a worker, while some
  graph-search setup is still fixed-cost and cannot yet be preempted.
- Progress is a coarse hand-built signal rather than a calibrated probability
  of root success.
- Candidate dependencies are represented by proof-context versions, not yet a
  first-class persistent AND/OR obligation DAG.
- The broker handles midpoint legs inside one mechanical action. Allocation
  across LLM calls, model search, Lean judge calls, and other worker families is
  the next generalization.
