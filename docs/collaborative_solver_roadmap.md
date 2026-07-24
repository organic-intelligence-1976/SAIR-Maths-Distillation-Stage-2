# Collaborative Solver Roadmap

This roadmap aligns the current baby solver with three long-term principles.

1. The LLM may propose arbitrary mathematical structure, especially midpoint
   lemmas, but every claim is mechanically proved or discarded.
2. Old high-coverage mechanical modules enter the new system through a tool
   contract instead of becoming a parallel solver bolted onto the side.
3. The LLM interface should not fossilize around today's model. Stronger future
   models should be able to send richer proof plans through the same soundness
   boundary.

## Target Architecture

The core object is a universal equation:

```text
UniversalEquation(name, variables, lhs, rhs)
```

Every true-side proof attempt should eventually have the same shape:

```text
prove(assumptions=[H, M1, M2, ...], target=G)
  -> Lean proof body or structured failure state
```

The LLM can then propose:

```json
{"kind": "midpoint", "lemma": "a ◇ (b ◇ b) = b"}
{"kind": "midpoint_chain", "lemmas": ["a ◇ a = b ◇ b", "a ◇ (b ◇ b) = a"]}
{"kind": "tool_call", "tool": "false_model_search", "routes": ["local_search:n=6:seed=2"]}
{"kind": "proof_plan", "steps": [{"claim": "...", "use": "..."}]}
```

The mechanical side proves each lemma before using it, stitches proved lemmas
into the final Lean body, and returns compact failure information when a claim
cannot be proved or consumed.

## Execution Phases

### Phase 1: Assumption-Aware Prover

Make the graph/grind prover consume named universal assumptions, not just the
original hypothesis `h`.

Quality gate:

- `prove([H], M)` works for simple LLM-proposed midpoint lemmas.
- `prove([H, M], G)` can instantiate `M` in the final goal proof.
- Existing focused tools still work.

### Phase 2: General Midpoint Stitcher

Add the recursive-looking but bounded first version:

```text
for M in LLM_midpoints:
    pM = prove([H], M)
    if pM:
        pG = prove([H, M], G)
        if pG:
            return stitch(M, pM, pG)
```

Then extend from one midpoint to a short chain where each lemma may use earlier
proved lemmas.

Quality gate:

- At least one live or replayed LLM hint not belonging to a hardcoded family is
  proved and used through the general stitcher.

### Phase 3: Mechanical Tool Contract

Port old solver modules behind one adapter:

```text
tool.run(assumptions, target, budget, state)
  -> ProofCandidate | LemmaCandidate | FalseModel | FailureState
```

Maturity levels:

- Wrapped: returns a proof/table if it finds one.
- Structured: returns frontier, generated facts, closest pairs, or failed
  bodies.
- Collaborative: consumes extra assumptions and helps prove subgoals.

Porting order:

1. false model finder and propagation modules;
2. h-instantiation / grind fact generators;
3. lemma and certificate harvesters;
4. proof batteries with strict scheduling;
5. specialized true-side modules after they can emit useful state.

### Phase 3B: Budget-Aware Scheduler

Replace hardcoded per-tool caps with a small dynamic scheduler that allocates
candidate depth from remaining budget and observed progress.

Motivation:

- `hard3_0145` showed that the clean solver missed a proof because native reference mechanical
  saturation stopped after three bodies, while the old reference accepted the
  fourth.
- A fixed cap can be useful as a narrow patch, but it should not become the
  long-term way we tune every imported module.

Target behavior:

```text
tool.describe_cost_curve()
tool.run(prefix_budget)
if stuck and progress looks promising:
    scheduler grants another body/route if budget remains
if LLM requests the same tool with a concrete reason:
    scheduler may grant a deeper slice
```

The scheduler state should track:

- remaining wall-clock and verifier/judge-call budget;
- already tried tool/body indices or false-search routes;
- phase: true-preferred, false-preferred, or balanced;
- winning body index and elapsed time for later tuning;
- whether the LLM or deterministic scheduler selected the attempt.

Quality gate:

- one known fixed-cap win, currently `hard3_0145`, is reproduced by policy
  rather than by a special constant;
- the policy does not regress the compact known true/false smoke;
- failed deeper slices produce useful feedback for System 2 instead of silent
  budget burn.

Status:

- First version implemented as `native_reference_true_v1`.
- Native true scheduling is now backed by
  `NATIVE_REFERENCE_TRUE_TOOL_PROFILES`: each imported true-side tool declares its
  cheap prefix, rough marginal cost, and depth character.
- `hard3_0145` is reproduced by policy: the default prefix keeps
  `deep_saturation` at 3 bodies, and a native true budget of at least 12 seconds
  grants `budget_extra_saturation` to body 4. The threshold was lowered from the first
  14-second observation because repeated runs showed upstream timing variation
  can leave the native true slice around 13.4 seconds.
- Attribution detail now records tool/body index, cap, total attempt index,
  generation elapsed time, remaining budget, cap-hit flags, and selected tool
  profile metadata.
- Regression artifacts:
  `.artifacts/native_gap_miner_hard3_0145_tool_profile_v1.json`,
  `.artifacts/native_gap_miner_hard3_0145_tool_profile_v1_summary.json`, and
  `.artifacts/native_gap_regression_tool_profile_v1.json`.

Next scheduler step:

- mine a second native-reference-only gap and either close it through an
  LLM/protocol repair or add the next evidence-backed tool-profile escalation.

### Phase 4: Bidirectional Feedback

Every serious tool failure should become compact state:

```json
{
  "target": "H => G",
  "status": "stuck",
  "proved_lemmas": [],
  "failed_midpoints": [],
  "left_frontier": [],
  "right_frontier": [],
  "closest_pairs": [],
  "tool_failures": []
}
```

The LLM response should be allowed to course-correct:

```json
{"kind": "repair", "replace_lemma": "...", "because": "..."}
```

Checkpoint in `baby_solver.py`:

- failed midpoint/lemma-chain hints now emit compact `SearchState` data;
- the state includes proved lemmas, failed midpoint claims, equality-component
  frontiers, closest pairs, and a `need_hint` bridge request;
- the next LLM round receives this state through `solver.mechanical_feedback`;
- false-model tool misses also feed back as structured tool feedback.

Follow-up checkpoint:

- the first LLM round now receives an initial direct-graph stuck state after
  deterministic routes fail;
- midpoint hints are cheaply filtered against tiny models of `H` before Lean
  proof search;
- unordered lemma-hint lists are ranked by goal overlap while explicit
  `midpoint_chain` / `lemma_chain` order is preserved;
- repeated failed tool or hint payloads are suppressed and reported instead of
  spending budget again;
- all tool calls that produce no body now emit structured feedback.

Sidecar-to-baby collaboration checkpoint:

- baby now shows sidecar-style problem analysis: h argument order, schematic
  `h` type, goal intro variables, and goal subterms;
- baby exposes a compact tool registry with aliases;
- ranked tool recommendations include executable calls, not just prose;
- `forward_saturation` is a real tool call that consumes LLM seed terms;
- shape-recognized cases run a collaboration-first LLM pass before deterministic
  focused helpers, with deterministic fallback preserved;
- accepted collaboration-first examples now include `hard2_0107`,
  `hard1_0018`, and `hard3_0231`, each solved by a live LLM tool/lemma-chain
  call followed by mechanical verification.

Reference mechanical tool integration checkpoint:

- `baby_solver.py` now includes a bounded proof-carrying superposition adapter
  from the reference baseline's `saturate_pc` lineage;
- the adapter is exposed as `goal_superposition` and also used as a fallback
  consumer for LLM-proposed midpoint/lemma chains;
- superposition step rendering was changed from broad `grind` to explicit
  `congrArg`/`trans` paramodulation proofs so judge axiom policies stay clean;
- `hard2_0107` now has a load-bearing generic path: an LLM-style
  `lemma_chain` proposes `u ◇ (v ◇ v) = v` and `u ◇ v = v ◇ v`, the
  superposition adapter proves those helpers from `H`, and the graph consumer
  stitches the goal;
- false-side `false_model_search` now supports `model_finder:n=k` propagation
  routes with per-size `none`/`budget`/`found` feedback, while preserving
  local-search routes.

System-1/System-2 protocol checkpoint:

- `docs/system1_system2_protocol.md` now records the working contract:
  System 1 is trusted mechanical machinery, System 2 is the untrusted strategist,
  and the protocol is the versioned adapter between them;
- baseline-style standard auxiliary lemmas are now exposed through
  `standard_aux_superposition`, which tries `const`, `proj_l`, `proj_r`, and
  `rowconst` as proof-carrying superposition targets before consuming any proved
  helper on the goal;
- official `hard3_0183` now has an accepted protocol-path smoke:
  a mocked LLM tool call to `standard_aux_superposition` produced a proof body
  accepted by the local judge, and the full `solve()` path returned
  `accepted_true_llm`;
- a live uptake probe first chose an unproved `lemma_hint`; after ranking
  one-sided-variable hypotheses toward `standard_aux_superposition`, live
  `gpt-oss-120b` selected that tool on `hard3_0183`, the tool proved `rowconst`,
  and the local judge accepted the resulting Lean;
- Lane A sweep now shows the tool is broad enough to harvest: 120/237 sampled
  hard-true-plus-normal-prefix cases built a standard-aux proof body under a
  3s aux budget, a balanced local-judge sample accepted 23/23, and a false-risk
  sample built 0/80 true bodies on false cases;
- the same sweep gives the next Lane A diagnosis: among 117 stuck cases, 22 had
  an auxiliary lemma proved but not consumed by the goal, while 27 failed at
  proving `rowconst`; this points to better aux-consumption/proof-node state and
  rowconst-focused superposition diagnostics before more prompt tuning;
- the first aux-consumption cure is in: `prove_with_assumptions_detailed` now has
  one larger graph tier when proved assumptions are present, and
  `standard_aux_superposition` now reports consumption-state feedback before the
  already-proved aux proof state. This moved 10/23 old `proved_not_consumed`
  cases to body-built, and all 10 accepted under the local judge;
- the next proof-node cure is in: when a standard aux lemma is proved but does
  not close the goal, `standard_aux_superposition` now tries bounded secondary
  bridges such as `opconst` and the missing opposite projection, proves that
  bridge from `H + aux`, and then stitches `H + aux + bridge => G`;
- this secondary bridge step solved 5/13 cases still stuck after the first cure:
  `hard1_0013`, `hard2_0004`, `hard2_0155`, `hard2_0198`, and `hard2_0200`.
  All five accepted under the local judge in
  `sidecar_runs/lane_a_secondary_bridge_verify_v1.jsonl`, with no constructed
  true bodies on the repeated 80-case false-risk sample;
- the superposition failure state now exposes more useful LLM telemetry:
  `target_shape`, derived closest equations, shape tags, and rowconst-specific
  bridge candidates. In `sidecar_runs/lane_a_superposition_state_diagnostics_v1.jsonl`,
  `hard1_0034` cannot prove rowconst directly, but the state points at a derived
  opconst-like equation `(v0 ◇ v1) = (v2 ◇ v3)` as the next bridge to ask for;
- this diagnostic has now produced a genuine generic-midpoint win:
  `hard1_0034` accepts when the LLM/mechanical protocol proposes the universal
  midpoint `a ◇ b = c ◇ d`; the generic midpoint engine proves that bridge from
  `H`, consumes it to close the goal, and the local judge accepts in
  `sidecar_runs/rowconst_diag_opconst_midpoint_hard1_0034_v1.jsonl`;
- live `gpt-oss-120b` initially overfit to a goal-specific bridge on
  `hard1_0034`, but after the feedback was tightened from "rowconst plus bridge"
  to "direct opconst when the diagnostic says opconst-like", it returned
  `{"kind":"midpoint","lemma":"a ◇ b = c ◇ d"}` and the generic midpoint proof
  accepted in `sidecar_runs/live_openrouter_hard1_0034_opconst_diag_repair_v2.jsonl`;
- the opconst repair generalizes: a bounded harvest over 49 rowconst-stuck cases
  built 13 direct-opconst midpoint bodies, and all 13 verified under the local
  judge in `sidecar_runs/harvest_opconst_midpoint_rowconst_stuck_verify_v1.jsonl`;
- `SuperpositionState.need_hint` now carries a concrete
  `recommended_next_action` when rowconst is stuck but an opconst-like derived
  equation appears, so the LLM no longer has to infer the intended bridge from
  raw shape tags alone;
- live first-attempt transfer checks on `hard1_0046` and `hard2_0065` followed
  that `recommended_next_action`, returned the direct opconst midpoint, and
  accepted after generic mechanical stitching. These are logged in
  `sidecar_runs/live_openrouter_hard1_0046_opconst_recommended_v1.jsonl` and
  `sidecar_runs/live_openrouter_hard2_0065_opconst_recommended_v1.jsonl`;
- the accepted-overlap audit in
  `sidecar_runs/lane_a_standard_aux_vs_deterministic_verify_sample_v1.jsonl`
  found 7/12 sampled cases accepted by `standard_aux_superposition` but not by
  deterministic baby candidates, including all five secondary-bridge wins. This
  gives the standard-aux lane an independent coverage signal rather than only a
  nicer interface to already-open deterministic cases;
- false-side misses now return a concrete continuation queue:
  `untried_requested_routes`, `recommended_next_call`, and a policy note
  preferring one untried local-search seed before broad larger-carrier jumps.
  Smoke states are logged in `sidecar_runs/false_route_continuation_feedback_v1.jsonl`;
- `hard1_0003` is now a live collaboration example from the old hard list:
  live `gpt-oss-120b` selected `standard_aux_superposition`, the tool proved
  `proj_r`, and the local judge accepted;
- the hint classifier was tightened so a non-hint tool call that happens to have
  a `lemmas` field is dispatched as a tool call, not accidentally interpreted as
  a generic lemma-chain payload;
- regression checks after that routing change: official `hard2_0107` accepts
  through the generic right-square `lemma_chain`, official `hard3_0231` accepts
  through the square-sandwich fallback after receiving its chain, and official
  `hard2_0016` still produces an accepted false certificate.

### Phase 5: Future-Model Headroom

The prompts may be tuned for current models, but the protocol should stay
semantic:

- equations, not only menu labels;
- assumption lists, not hardcoded family names;
- proof nodes and failure states, not raw transcripts by default;
- optional Lean snippets and errors when repair is useful.

This lets a weak model choose tools and simple lemmas, while a stronger model
can propose multi-rung midpoint chains or proof plans without changing the
soundness boundary.

## Current Critical Path

```text
UniversalEquation / assumption records
-> assumption-aware graph prover
-> general midpoint-chain stitcher
-> LLM arbitrary midpoint protocol
-> old-module adapter contract
-> scheduler and structured failure feedback
```

The rule for moving fast is:

```text
Wrap quickly.
Measure usefulness.
Add structure where it helps.
Make collaborative only when the module earns that investment.
```
