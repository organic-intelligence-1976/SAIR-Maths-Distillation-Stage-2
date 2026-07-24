# Native Import Contract

This document defines how external mechanical ideas should enter the
collaborative solver without becoming another hidden fallback. The embedded
reference mechanical source and child solver were retired on 2026-07-23 after
attribution showed no child-only winners and minimal native forms were added for
the remaining mechanism categories.

## Boundary Goal

Every imported mechanical idea should become a protocol tool:

- callable by this project's scheduler or by an LLM `tool_call`;
- trusted only after local Lean or countermodel verification;
- able to report structured failure state when it does not solve;
- attributed separately from other native tools and from LLM-load-bearing
  actions.

The retired fallback must not be reintroduced as a safety net. An external
reference solver belongs in an evaluation harness, not inside the submission.

## Tool Metadata

Each protocol tool must declare these fields in `TOOL_REGISTRY`:

| Field | Meaning |
|---|---|
| `domain` | `true` or `false`. |
| `scope` | `whole_goal`, `subgoal`, or `both`. |
| `cost` | `cheap`, `medium`, or `expensive`. |
| `feedback_quality` | `minimal`, `basic`, `structured`, `rich`, or `judge_exact`. |
| `native_import` | Implementation/status tag such as `native_graph`, `native_superposition`, or `native_false_routes`. |

The protocol-visible contract is attached to tool states as `tool_contract`.

`scope` is intentionally about capability, not implementation. A tool marked
`both` should be usable for the original `H => G` and for an LLM-proposed target
such as `H => M`. If a tool cannot safely prove arbitrary subgoals yet, mark it
`whole_goal` and do not route midpoint legs through it.

## Success Contract

A successful native import must return one of:

- a Lean proof body that the official judge accepts for `true`;
- a false certificate table or formula that the official judge accepts for
  `false`;
- a subgoal proof body that can be stitched under a verified midpoint or lemma
  chain.

Success is not trusted because it came from the reference mechanical baseline.
It is trusted only because the collaborative solver verifies the artifact.

## Failure Contract

A failed native import should return a protocol state with:

- `protocol_version`;
- `kind`;
- `status`;
- `source`;
- `tool_contract`;
- `attempt` or `trials` describing budget/routes/limits;
- `need_hint`;
- `suggested_next_actions` when the next step is mechanical and executable;
- compact evidence of partial progress, such as generated equations,
  closest-pairs, forced assignments, blocked cells, proved-but-unused lemmas, or
  exhausted carrier sizes.

Minimal `not_applicable` feedback is acceptable for cheap focused tools. Broad
or expensive tools should produce `structured` or `rich` feedback.

## Import Levels

Use these levels to avoid pretending that a partial port is complete.

| Level | Meaning |
|---|---|
| 0 | Only available through the child fallback. |
| 1 | Callable natively on whole goals, but feedback is shallow. |
| 2 | Callable natively with structured feedback and attribution. |
| 3 | Usable as a subgoal consumer for midpoint/lemma recursion. |
| 4 | Integrated into scheduler with measured budget behavior and no child-only wins for its niche. |

B+ for an import family is usually level 2 or 3. Retiring the child fallback
requires level 4 coverage for all niches where the child fallback still wins.

## Broad Certificate Pipeline

Do not import the reference baseline's broad certificate pipeline as one opaque `certificates`
tool unless it is only a temporary diagnostic wrapper. Split it into stages or
families that can report why they did not apply:

- detected H shape;
- candidate helper/certificate family;
- helper equations derived or rejected;
- final close attempt;
- next stronger helper the LLM could propose.

The first native target should be the smallest family responsible for a
child-only win, not the whole pipeline.

## Scheduler Policy

Do not solve the full scheduler up front. Until enough attribution data exists:

- cheap tools may run early;
- expensive tools run late unless explicitly selected by the LLM;
- repeated failed tools are suppressed;
- tools with `scope: both` may be tried on midpoint legs;
- deep source-independent portfolios remain late unless attribution justifies
  moving them earlier.

After several native imports, revisit scheduler design using attribution data:

- solved by the native collaborative solver;
- solved by an imported reference mechanical tool;
- solved by LLM-selected tool/midpoint;
- solved only by child fallback;
- unsolved after child fallback.

### Adaptive Scheduler Target

The original `hard3_0145` saturation-cap fix was deliberately a local patch,
not the final scheduling philosophy. It showed that a fixed cap can stop one
body before a useful proof. The current source-independent late portfolio uses
remaining wall-clock budget to sequence grounding, auxiliary superposition,
deep saturation, and broad goal superposition; richer allocation remains a
future empirical task.

Each protocol tool should eventually expose enough metadata for the scheduler
to decide whether another body/route is worth buying:

- default cheap prefix;
- marginal cost of the next candidate;
- historical hit rate by candidate depth or route family;
- whether later candidates are qualitatively new or just broader flooding;
- whether recent failure feedback shows a near miss.

The scheduler should receive a remaining-budget view:

- wall-clock budget left;
- judge-call / verifier-cost budget left;
- phase (`true_preferred`, `false_preferred`, or `balanced`);
- previous failed tools and body indices;
- whether the LLM explicitly requested a deeper slice after seeing feedback.

Initial policy sketch:

- run a conservative cheap prefix by default;
- grant one or two extra bodies when the tool reports promising progress or an
  LLM asks for that tool with a concrete rationale;
- save expensive deep slices for late/final passes or high-confidence
  reference-gap rows;
- record the winning body index, elapsed time, and attribution so later caps are
  learned from evidence rather than hand-tuned constants.

Fixed caps remain acceptable as short-term patches only when a native-gap probe
identifies a specific missed body and the rerun proves the gap closes.

## Retirement Rule

The removal gate was satisfied: representative attribution showed no important
`child_reference_fallback` unique wins. The source-independent solver retains a
minimal native representative of each formerly fallback-only category:

- `deep_saturation`;
- `grounding_h`;
- `structured_ce`.

`scripts/native_import_audit.py` now fails if embedded-source, namespace, or
whole-child fallback markers reappear. A future reference-only win should be
recovered by implementing the smallest responsible mechanism behind the normal
tool contract, then rerunning the same focused comparison.

## Optional External Engines

Optional local engines are allowed only when they are wrapped as ordinary
protocol tools and degrade cleanly. If a dependency is absent, the tool should
return a structured `unavailable`/`no_countermodel_found` state rather than
crashing or changing the outer loop.

Current example: `false_model_search` accepts `cp_sat:n=k`. When OR-Tools is
available, this route performs exact finite-domain countermodel search and
reports per-skolem `INFEASIBLE`/`UNKNOWN` telemetry; otherwise it reports that
the route is unavailable.

## LLM-First Tie-Breaker

When a fallback or partial-native failure can be fixed either by importing more
reference mechanical machinery or by improving LLM/mechanical cooperation, try
the LLM route first.

Prefer an LLM-orchestration probe when the missing move can plausibly be
expressed as:

- a midpoint equation;
- a short lemma chain;
- a repaired over-specific helper;
- better seed terms or `seed_h_args`;
- a concrete false-model route, size, or seed choice.

Example: `hard3_0202` was a partial-native true failure, but the missing move
was expressible as the midpoint `a ◇ ((b ◇ c) ◇ d) = a ◇ b`. Improving
SearchState feedback and helper consumption solved it without importing a new
reference mechanical module.

Prefer native import first only when the existing mechanical consumers cannot
verify the proposed kind of help. Examples include a missing certificate family,
a missing counterexample family, or a subgoal proof engine that cannot yet
consume the helper the LLM would need to supply.

The practical triage order is:

```text
fallback or partial-native failure
=> can System 2 describe a useful bridge/route/repair?
   yes: improve feedback/prompt/normalization and test an LLM probe
   no: import the smallest responsible reference mechanical component natively
=> rerun attribution
```

Use `scripts/fallback_triage.py` after attribution reports. It marks actual
child-fallback winners and also flags failed partial-native routes, such as
`deep_saturation` or `goal_superposition`, as LLM-orchestration candidates
before native import candidates.

## Native Gap Miner

Use `scripts/native_gap_miner.py` when the question is "which native mechanism
should be improved next?"

The script packages the current source-independent `baby_solver.py` and compares
it with an explicit `--reference-solver` or `--reference-submission`. Without
one, the second run is only an identical-control packaging check.

It then runs both through the official pipeline, compares accepted rows, and
groups reference-only wins into import buckets such as certificate pipeline,
saturation bodies, superposition bodies, model-finder/propagation, or
counterexample family.

Recommended usage:

```bash
python3 scripts/native_gap_miner.py \
  --problems .artifacts/expected_win.jsonl \
  --config .artifacts/openrouter_fast_config.json \
  --id hard2_0107 \
  --output-json .artifacts/native_gap_miner_one_row.json \
  --output-md .artifacts/native_gap_miner_one_row.md
```

Use `--id` repeatedly or comma-separated, and use `--max-problems` for quick
slices. The miner is intentionally a planning harness, not a broad benchmark.
The first validated checks were:

- `.artifacts/native_gap_miner_expected_win_v2.md`: 5/5 clean solver, 5/5
  reference, zero reference-only gaps;
- `.artifacts/native_gap_miner_one_row.md`: filtered one-row probe completed
  quickly and confirmed the harness works for small candidate rows.
- `.artifacts/native_gap_miner_reference_hard3_oldwins_fast.md`: first real
  reference-only gap. An older generated solver artifact solved `hard3_0145`,
  while the clean solver did not.
- `.artifacts/native_gap_miner_reference_hard3_oldwins_after_saturation_cap_minimal.md`:
  after importing the missing bounded native saturation slice, clean solver also
  solves `hard3_0145` and the reference-only gap disappears.

If a mixed probe becomes slow, narrow the input instead of treating the miner as
the next benchmark. The workflow is:

```text
suspected reference-only row
=> run tiny native_gap_miner probe
=> inspect ranked import bucket
=> either improve LLM/protocol if a bridge/route could express the missing move
   or port the smallest responsible reference mechanical component natively
=> rerun the same tiny probe
```

Historical first import lesson:

```text
hard3_0145
=> old reference accepted a true HAVE+GRIND proof in the fourth saturation body
=> the then-current native wrapper had tried only the first three saturation bodies
=> raise the bounded saturation cap from 3 to 4
=> rerun the same two-row old-win probe; reference-only gaps drop from 1 to 0
```

Current replacement:

```text
hard3_0145
=> source-independent deep_saturation emits four bounded certificate bodies
=> the late native portfolio judges them under a shared remaining-time budget
=> direct official-judge checks accept all four current bodies on this row
=> the compiled solver solves the row without an available LLM credential
```

Evidence:

- `.artifacts/native_gap_miner_hard3_0145_scheduler_policy_v1.json`
- `.artifacts/native_gap_miner_hard3_0145_scheduler_policy_v1_summary.json`
- `.artifacts/native_gap_regression_scheduler_policy_v1.json`
- `.artifacts/native_gap_miner_hard3_0145_tool_profile_v1.json`
- `.artifacts/native_gap_miner_hard3_0145_tool_profile_v1_summary.json`
- `.artifacts/native_gap_regression_tool_profile_v1.json`
