# Native Import Pass, 2026-07-24

This note records a focused import/validation pass after reviewing a newer
high-coverage mechanical solver recommendation. The goal was to pull useful
mechanical ideas into the public collaborative solver without reintroducing an
opaque fallback.

## Imported

- Added a sandbox-legal `sympy_sat` route under the existing
  `false_model_search` protocol tool.
- Added `collapse_certificates` as a first-class true-side protocol tool.
- Added `broad_grounding_derived` as a first-class true-side protocol tool.
  The default route uses a split helper budget; full per-helper budget remains
  an explicit diagnostic option because some generated helpers can make Lean's
  final `grind` close too expensive.
- Exposed `grounding_h` earlier in the trusted true-candidate portfolio.
- Added a deterministic false-route promotion step: if propagation search gets
  close and emits an exact-search continuation, the solver follows that route
  before asking the LLM.

## Focused Verification

All rows below were run through the compiled single-file submission and the
official proxy/judge locally. Solver timeout was 180 seconds.

| Problem | Expected | Verdict | Solved | LLM calls | Judge calls | Elapsed |
|---|---:|---|---:|---:|---:|---:|
| `hard1_0009` | false | false | yes | 0 | 2 | 81.52s |
| `hard3_0058` | true | true | yes | 0 | 1 | 1.79s |
| `hard3_0278` | true | true | yes | 0 | 1 | 2.94s |
| `hard3_0279` | true | true | yes | 0 | 1 | 3.25s |
| `hard1_0013` | true | true | yes | 0 | 1 | 8.38s |
| `hard1_0034` | true | true | yes | 0 | 2 | 4.19s |
| `hard1_0046` | true | true | yes | 0 | 2 | 5.97s |
| `hard1_0054` | true | true | yes | 0 | 1 | 1.98s |

Additional repo checks passed:

- `python3 -m py_compile baby_solver.py`
- `python3 scripts/research_system_contracts.py`
- `python3 scripts/native_import_audit.py`
- `python3 scripts/compile_submission.py`
- `python3 scripts/compiled_submission_smoke.py --solver-timeout 120 --judge-timeout 120`

## Caveat

The first safe import did not solve every broader cascade row. In particular,
`hard2_0178` originally generated a useful grounding-derived helper whose final
Lean close did not discharge the goal. The later standard-aux focus pass below
resolved that row through a cleaner projection-lemma route, so broad
grounding-derived still remains a diagnostic/certificate tool rather than the
primary route for this pair.

## Follow-up: Forward Saturation Battery

A later focused pass found that the native saturation code existed but did not
match the proven forward-saturation instance generator: it added too many
diagonal rows and could truncate away the useful generated instances. The solver
now uses the bounded feed-forward generator in the early true-candidate stream,
before the older flat HAVE+GRIND fallback.

Direct judge checks of the generated saturation bodies:

| Problem | First accepted route | Result |
|---|---|---|
| `hard2_0021` | `deep_saturation:d=2:slots=1:haves=10` | accepted |
| `hard3_0193` | `deep_saturation:d=3:slots=2:haves=37` | accepted |
| `hard3_0196` | `deep_saturation:d=2:slots=1:haves=13` | accepted |
| `hard3_0307` | `deep_saturation:d=3:slots=3:haves=46` | accepted |

The compiled submission also returned `verdict=true` for all four rows through
the official proxy with zero LLM calls. This is a native mechanical import, not
a load-bearing LLM win.

Follow-up adapter fix: an LLM `forward_saturation` tool call now verifies the
generated saturation bodies cheapest-first and returns the first accepted body.
This matters because later saturation bodies can fail even when an earlier body
closes the goal (`hard2_0021` is an example). A fake-LLM test confirmed the
collaboration loop returns `accepted_true_llm` when the tool call succeeds
internally.

## Follow-up: Derived Standard Aux Focus

The next recommendation group was `hard2_0178` / `hard3_0271`. The archived
mechanical solver won these by deriving full standard projection lemmas and then
closing the goal:

| Problem | Derived helper | Compiled solver result |
|---|---|---|
| `hard2_0178` | `∀ a b : G, a ◇ b = a` | true, 1 judge call, 0 LLM calls, 6.52s |
| `hard3_0271` | `∀ a b : G, a ◇ b = b` | true, 1 judge call, 0 LLM calls, 7.84s |

The native fix was not a new opaque fallback. `standard_aux_superposition` now
uses a cheap refutation scout to order plausible standard aux lemmas, proves the
chosen helper with proof-carrying superposition, and tries ordinary
non-overlap superposition before the more explosive variable-overlap fallback.
The protocol state reports `implied_aux`, per-helper budgets, and whether a
failed helper was budget-starved.

One recommendation group remains open:

- `hard3_0204` / `hard3_0210`: midpoint-chain candidates. A repeated
  self-absorption strategy card and early true-side LLM checkpoint were added,
  with midpoint-chain mechanical work capped in that pass. A live trace showed
  the checkpoint is reached promptly, but no new accepted proof has been
  established yet.
