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

## Packed rigidity portfolio

The packed submission now applies the same renewable-grant principle when an
exhaustive size-2-through-4 scan finds no nontrivial model of the hypothesis.
That scan remains routing evidence only. The scheduler probes one entry rung
from each registered collapse family, ranks a proved entry above a compact
proof-carrying frontier, and renews only supported continuations. Every winning
route still emits the full Lean proof.

These in-process superposition grants are charged against CPU time and bounded
again by the problem's remaining wall-clock deadline. This prevents host load
from shrinking a four-second search into a much smaller amount of mathematical
work while preserving a hard real-time ceiling. Resource-heavy 40-plus-instance
`HAVE+GRIND` bodies remain useful discovery telemetry, but are not sent to the
judge unless converted into a structured certificate.

Capability checks on 2026-08-06:

- both known collapse families certify at a 60-second advertised budget with
  zero LLM calls and one judge call;
- both still certify while six independent CPU burners run concurrently;
- the 20-case true/false risk set certifies 20/20 with no verdict mismatch.

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
