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

The broader cascade rows from the recommendation are not fully solved by this
safe import. In particular, `hard2_0178` can generate a useful
grounding-derived helper under a full per-helper budget, but the final Lean
close may run too long. The automatic solver therefore keeps the safe split
budget by default. The next principled improvement is an explicit final closer
for broad grounding-derived helpers, or a pre-judge risk filter that avoids
submitting expensive `grind` closes.
