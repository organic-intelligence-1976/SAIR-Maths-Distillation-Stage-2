# LLM Lean Sidecar Prototype

`scripts/llm_lean_sidecar.py` is a small experiment harness for the LLM/prover
interface. It is intentionally outside the generated competition `solver.py`.

The sidecar tests one problem at a time. Most modes target true-side proofs,
while `false_model_hint` targets finite countermodels:

1. load a SAIR problem;
2. build a compact prompt describing the Lean wrapper and the current mechanical
   analysis;
3. accept either a local candidate proof body or an LLM JSON response;
4. lightly clean common scaffolding mistakes;
5. verify the wrapped body with the official judge;
6. write a JSONL transcript containing the prompt, raw body, cleaned body, Lean
   code, and compact Lean feedback.

The expected LLM payload is deliberately simple:

```json
{"kind":"goal_proof","proof":"intro x y\nhave h1 := h x x x\ngrind"}
```

The proof is not trusted. The sidecar wraps it as the body after:

```lean
intro G _ h
```

and accepts it only if the judge accepts the resulting Lean file.

There is also an `hargs` mode where the LLM does not write Lean proof text.
Instead it returns extra instantiations of `h`:

```json
{"kind":"h_arg_hints","h_args":[["x","x ◇ y","y"]]}
```

The sidecar canonicalizes these terms, adds them to its generated h-fact graph,
tries to synthesize a `calc` proof mechanically, and then verifies that proof.

There is also a `tool_call` mode where the LLM does not provide Lean or raw
`h` arguments. Instead it selects a trusted mechanical module and a small set of
seed terms:

```json
{
  "kind": "tool_call",
  "tool": "forward_saturation",
  "target": "goal",
  "seed_terms": ["x ◇ y", "y ◇ y"],
  "budget": 3,
  "why": "Generate h-instances around the repeated y-square terms."
}
```

Supported tools:

- `proof_battery`: runs the old deterministic HAVE+GRIND battery. It is useful
  as a cheap source of verifier feedback. It now first tries an explicit
  h-fact graph proof over the old battery's generated h-instance layers, then
  falls back to the original `grind` bodies when no graph path is found.
- `forward_saturation`: generates h-instantiations from goal terms plus the
  LLM's seed terms, then first tries the h-fact graph renderer to build an
  explicit `calc` proof. If no graph path exists, it falls back to a bounded
  `grind` body. Failures report generated terms, h-argument rows, trial configs,
  consumer (`h_fact_graph` or `grind`), and a next `need_hint`.
- `goal_superposition`: runs the proof-carrying superposition module on the full
  goal. By default this tool does not run the slower implied-auxiliary-lemma
  detector; callers can opt in with `"include_aux": true`.
- `square_sandwich_chain`: tries the square-constant/right-identity/sandwich
  renderer for hypotheses of the form `x = ((y ◇ x) ◇ y) ◇ (z ◇ z)`. This is the
  tool-call version of the helper chain used for cases such as `hard3_0231`.
- `right_square_chain`: tries the right-square/square-absorption renderer for
  hypotheses of the form `x = (y ◇ (y ◇ z)) ◇ (x ◇ x)`. It proves helper
  equations equivalent to `u ◇ (v ◇ v) = v` and `u ◇ v = v ◇ v`, then stitches
  supported goals explicitly.
- `certificates`: runs a small slice of the old solver's proof-certificate
  renderers. It is broader than `square_sandwich_chain`, but still returns only
  verifier-checked Lean or structured attempt feedback.
- `rowconst_certificates`: runs the focused row-constant and square-rowconstant
  certificate renderers that used to be hidden inside `certificates`.
- `grounding_derived`: runs the old grounding-derived certificate renderer
  directly. It now first tries a focused explicit square-rowconst closer for
  the `x = (x◇x)◇((y◇z)◇z)` niche, then falls back to the old renderer and
  reports the derived helper/body excerpt when the final close fails.
- `lemma_hint`: adapts a tool call into the existing lemma-hint consumer. The
  LLM supplies one equation or a short `lemmas` list; the sidecar must
  mechanically prove the lemma and then use it to close the goal.
- `lemma_chain`: adapts a tool call into the existing lemma-chain consumer. It
  can consume square-witness helper chains and right-square helper chains such
  as `u ◇ (v ◇ v) = v`, `u ◇ v = v ◇ v`; failures report which helpers could
  not be proved or why the proved helpers did not connect the goal graph.
- `false_model_search`: adapts a tool call into the existing false-side finite
  countermodel machinery. It accepts the same controls as `false_model_hint`
  (`template`, `sizes`, `seeds`, `routes`, `focus_cells`, optional full table),
  and still verifies any candidate table before accepting.

Example no-LLM smoke test:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id normal_0121 \
  --mode tool_call \
  --candidate-json-file sidecar_runs/tool_call_forward_saturation_seed.json \
  --rounds 1 --no-llm
```

Square-chain smoke test:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id hard3_0231 \
  --mode tool_call \
  --candidate-json-file sidecar_runs/tool_call_square_sandwich_chain_seed.json \
  --rounds 1 --no-llm
```

Right-square-chain smoke test:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id hard2_0107 \
  --mode tool_call \
  --candidate-proof '{"kind":"tool_call","tool":"right_square_chain","target":"goal","budget":15}' \
  --rounds 1 --no-llm
```

Generic right-square lemma-chain smoke test:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id hard2_0107 \
  --mode tool_call \
  --candidate-proof '{"kind":"tool_call","tool":"lemma_chain","target":"goal","lemmas":[{"name":"square_absorb","equation":"u ◇ (v ◇ v) = v"},{"name":"right_square","equation":"u ◇ v = v ◇ v"}]}' \
  --rounds 1 --no-llm
```

Certificate smoke test:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id hard3_0183 \
  --mode tool_call \
  --candidate-json-file sidecar_runs/tool_call_certificates_seed.json \
  --rounds 1 --no-llm
```

Focused rowconst certificate smoke test:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id hard3_0183 \
  --mode tool_call \
  --candidate-proof '{"kind":"tool_call","tool":"rowconst_certificates","target":"goal","budget":15,"max_candidates":2}' \
  --rounds 1 --no-llm
```

False-side tool-call table verification smoke test:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id hard2_0016 \
  --mode tool_call \
  --candidate-proof '{"kind":"tool_call","tool":"false_model_search","target":"goal","template":"local_search","table":[[5,0,0,0,0,2],[1,3,1,2,1,1],[5,3,2,2,2,2],[4,3,3,5,3,4],[4,4,4,0,4,1],[5,4,5,5,5,1]],"budget":1}' \
  --rounds 1 --no-llm
```

False-side search-only smoke test:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id hard2_0016 \
  --mode tool_call \
  --candidate-proof '{"kind":"tool_call","tool":"false_model_search","target":"goal","template":"local_search","routes":["local_search:n=6:seed=2"],"budget":5}' \
  --rounds 1 --no-llm --false-search-budget 5
```

False-side stuck smoke test:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id hard2_0027 \
  --mode tool_call \
  --candidate-proof '{"kind":"tool_call","tool":"false_model_search","target":"goal","template":"focused_local_search","routes":["local_search:n=6:seed=0"],"budget":1}' \
  --rounds 1 --no-llm
```

`tool_call` prompts now include a small mechanical tool-selection ranking. It is
pure advice: the ranker checks cheap shape facts, recent failed tools, and
`module_state.need_hint.next_tool_call_shape` from previous attempts. The LLM may
follow it, override it, or use it to explain why another tool is better.
When the mechanical tools are exhausted, the same block may include
`llm_only_actions`: these are templates such as `lemma_hint` that the auto-router
cannot fill, but the LLM can complete with concrete bridge equations.

For deterministic no-network testing of the same interface, use
`--auto-tool-router`. This makes the local ranker emit the JSON tool call that
an LLM would normally choose, then sends that call through the normal
tool-runner/Lean-verifier path:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id normal_0121 \
  --mode tool_call \
  --auto-tool-router \
  --rounds 1 --no-llm
```

The transcript records both the initial `tool_recommendations` object and the
per-round `tool_router` event, so live LLM selections can be compared against
the deterministic router later.

Tool calls can also carry untrusted bridge equations:

```json
{
  "kind": "tool_call",
  "tool": "lemma_hint",
  "target": "goal",
  "lemmas": ["a ◇ b = a ◇ c", "x ◇ y = x"],
  "why": "Try small bridge equations after saturation and superposition both got stuck."
}
```

These are still verifier-backed: a bad lemma is rejected or returned as a
structured failed hint, not assumed.

When prior attempts show that repeated mechanical tools are stalled and the
recommendation block has an LLM-only action, the sidecar now rejects another
plain `forward_saturation`/`goal_superposition` retry with `NEEDS_LEMMA_TOOL`.
The LLM can still intentionally override with `override_repeated_tool: true`,
but the default path is to fill the lemma/midpoint template.

The adapter also tolerates a common LLM repair typo: if a `lemma_hint` tool call
returns `seed_h_args_template` as actual rows, the sidecar treats it as
`seed_h_args` and attaches those rows to each lemma candidate.

When `forward_saturation` gets stuck after generating h-instances, its
`llm_tool_call_templates` now include concrete `seed_h_args` rows copied from
that failed run. The LLM still has to supply the bridge equation, but it does
not have to rediscover the exact h-row syntax from scratch.

When `lemma_hint` itself gets stuck, the tool-call adapter now carries the same
idea forward: repair templates include proved-but-unused equations, the exact
missing bridge, and recent seed h-rows recovered from earlier mechanical states.
This lets the next LLM round edit a concrete bridge attempt instead of inventing
both the equation and the instantiation rows from a blank page.

The next interface level is `lemma_hint` mode. Here the LLM proposes one
equational intermediate lemma, optionally with seed h-instantiations for proving
it and argument tuples for using it:

```json
{
  "kind": "lemma_hint",
  "equation": "x ◇ y = x ◇ z",
  "seed_h_args": [["x", "y", "z"]],
  "use_args": [["x", "y", "z"]]
}
```

The lemma is still untrusted. The sidecar first creates a temporary problem with
the original `H` and the proposed lemma as `G`, synthesizes a graph proof, and
asks the official judge to check it. Only after that succeeds does it introduce
the lemma as `have mid : ... := by ...` and try to prove the original goal using
`mid` as another rewrite source.

When the h-fact graph cannot close a leg, the sidecar now records a
`SearchState`: component sizes for the goal-left and goal-right terms, sample
terms in each component, closest-looking frontier pairs, and graph settings such
as congruence depth. This is shown back to the LLM in later rounds.

The graph can also add bounded congruence edges:

```bash
--congruence-depth 2 --max-congruence-facts 1200
```

This preserves simple graph wins while giving the LLM better feedback about
where the equality search is stuck.

The current `SearchState` keeps the earlier graph-specific fields, but now also
exposes the stable planning contract:

- `goal`, `status`, `proved_facts`
- `left_frontier`, `right_frontier`
- `proved_lemmas`, `failed_hints`
- `missing_bridge`, `need_hint`
- `budget_used`

`need_hint` is the compact request intended for the next LLM round, for example:

```json
{
  "need_hint": "prove these two terms equal",
  "left_term": "...",
  "right_term": "...",
  "reason": "This equality would connect the current goal-left and goal-right graph components."
}
```

Every new attempt transcript also gets a normalized `CollaborationState`. This
is the prompt-facing summary shared by true and false modes. It is intentionally
smaller than the raw logs:

## Scoreboard

`scripts/sidecar_scoreboard.py` summarizes sidecar JSONL transcripts into a
small flywheel dashboard:

```bash
python3 scripts/sidecar_scoreboard.py sidecar_runs/*.jsonl --max-rows 40
```

The scoreboard reports accepted/stuck/structured-feedback signals, tool calls,
accepted tools, top errors, and the last `need_hint` for each transcript. This
is the default measurement layer before adding more old solver machinery.

```json
{
  "kind": "collaboration_state",
  "status": "incorrect",
  "error_code": "FALSE_HINT_NO_MODEL",
  "hint": {"kind": "false_model_hint"},
  "mechanical": {
    "false_search": {
      "tried_routes": ["local_search:n=6:seed=0"],
      "untried_requested_routes": ["local_search:n=6:seed=1"]
    }
  },
  "proved_artifacts": [],
  "failed_hints": [],
  "need_hint": {"need_hint": "propose a different finite-countermodel search hint"},
  "budgets": {"false_search_remaining": 12.0}
}
```

For true-side attempts, the same object summarizes graph component sizes,
proved-but-unused lemmas, lemma-chain normal forms, and the next missing bridge.
For false-side attempts, it summarizes tried routes, skipped routes, budget
remaining, and countermodel source if one was found. Later prompts show this
normalized state before the detailed `SearchState`/`module_state` blocks.

False-side local search now emits lightweight near-miss diagnostics. For each
failed local-search route, the sidecar records the best table it saw by H
violation count, then reports:

- H violation count/ratio and H-hotspot cells;
- G failure count/ratio and G-failure hotspot cells;
- a small table profile: diagonal, row uniqueness, constant rows, sampled
  commutativity failures;
- an interpretation such as “G can already fail in near-models; repair H
  hotspots” or “H is satisfied but G still holds; try a G-breaking
  size/template.”

These diagnostics are computed cheaply during the repair loop and expanded only
once at the end, so they do not replace the actual countermodel search.

The first consumer for those diagnostics is `focused_local_search`. It accepts
structured cell hints:

```json
{
  "kind": "false_model_hint",
  "template": "focused_local_search",
  "routes": ["local_search:n=6:seed=2"],
  "focus_cells": [[1, 2], [1, 3]],
  "freeze_cells": [{"cell": [0, 0], "value": 0}],
  "bias_cells": [{"cell": [1, 2], "values": [0, 3]}],
  "constraints": ["repair H-hotspot cells while preserving G failure"]
}
```

`focus_cells` bias repair moves toward H-hotspot cells, `freeze_cells` pin known
cell values, and `bias_cells` prefer selected values for selected cells. A
G-breaking focused hint can also ask the search to perturb goal-relevant cells
instead of immediately restarting when it finds an H-model where G still holds.

For `lemma_hint`, the prompt also emits machine-readable standard-helper advice.
When the small-model filter says a helper is plausible, the LLM is asked to
include it directly in the candidate list:

```json
{
  "include_standard_helpers": ["a ◇ b = a ◇ c"],
  "reason": "small-model filter did not refute these helpers; include them as candidates"
}
```

`lemma_hint` also has optional stronger mechanical consumers:

- `--lemma-superposition-budget`: try proof-carrying superposition when the
  graph cannot prove the proposed lemma.
- `--midpoint-superposition-budget`: try the solver's midpoint stitcher when a
  proved lemma is not enough for the graph to close the original goal.
- `--standard-lemma-cert-budget`: when the LLM proposes an implied standard
  lemma such as rowconst (`a ◇ b = a ◇ c`), try specialized verified consumers.

The first specialized no-grind renderer covers hypotheses of the form
`x ◇ y = y ◇ (z ◇ (y ◇ z))`. If the LLM proposes rowconst, the sidecar proves a
column-invariance helper, proves rowconst explicitly with `calc` and `congrArg`,
and closes compound-product goals without relying on `grind`.

The second specialized no-grind renderer covers hypotheses of the form
`x = (x ◇ x) ◇ ((y ◇ z) ◇ z)`. When the LLM proposes rowconst, the sidecar proves
the useful `a ◇ b = a ◇ a` consequence explicitly and closes goals such as
`hard3_0183`.

`lemma_hint` now accepts either one equation or a short candidate list via
`lemmas`, `lemma_hints`, `candidates`, or `equations`. Candidates are ranked by
cheap SearchState-style features: standard helper shape, overlap with goal
terms, small size, and low arity. Each candidate is still fully verified before
acceptance.

For proved-but-unused lemmas, the sidecar emits `lemma_instance_diagnostics`:
how many instances were tried, which ones touched the left or right goal
component, and whether any instance bridged both components.

The parser also performs a conservative syntax repair for a common LLM typo:
if one side of an equation has missing final close-parentheses, the sidecar
balances that side before parsing and records the `syntax_repair` in the
candidate summary. The repaired lemma is still only accepted if the mechanical
prover and Lean verify it.

The next interface level is `lemma_chain` mode. Here the LLM returns a short
list of universal helper equations instead of one midpoint. The first supported
chain is the witness-square proof shape for hypotheses
`x = ((y ◇ x) ◇ y) ◇ (z ◇ z)`:

```json
{
  "kind": "lemma_chain",
  "lemmas": [
    {"name": "square_const", "equation": "u ◇ u = v ◇ v"},
    {"name": "right_id_square", "equation": "u ◇ (v ◇ v) = u"},
    {"name": "sandwich", "equation": "(v ◇ u) ◇ v = u"},
    {"name": "left_sandwich", "equation": "v ◇ (u ◇ v) = u"}
  ],
  "witness_term": "x ◇ x"
}
```

The sidecar proves these helpers explicitly with `calc`, `rw`, and `congrArg`.
The fourth helper is derived from the first three plus one more H-instantiation,
so older three-lemma chain replays can still activate it mechanically. The
sidecar then runs a tiny simplifier using only those proved helpers. If both
sides of the goal reduce to the same term, the rendered proof is judge-checked.
If the chain is incomplete or the simplifier does not close the goal, the
transcript records the missing helper kinds or the two normal forms.

The false-side interface is `false_model_hint`. The LLM does not write Lean and
does not claim the verdict; it proposes search controls for finite model
finding:

```json
{
  "kind": "false_model_hint",
  "template": "local_search",
  "sizes": [5, 6, 7],
  "seeds": [0, 1, 2],
  "time_budget": 18,
  "constraints": ["noncommutative", "allow repeated rows"]
}
```

The sidecar consumes these hints with local search, bounded propagation/model
finding, or small closed families. A found table is checked twice: first by the
Python evaluator to ensure `H` holds and `G` fails, then by the official Lean
judge. For Lean, the sidecar emits an axiom-clean finite operation as a plain
function over `Fin n` and closes the certificate with `decideFin!`; this avoids
the older table helper path that could trigger the judge's axiom audit.

For broad local-search hints, the scheduler now tries one `(size, seed)` at a
time, prioritizing the sizes that have been useful for hard finite
countermodels. This prevents a vague hint such as `sizes: [5, 6, 7]` from having
its budget split twice before size 6 gets a real chance. The LLM may suggest a
`time_budget`, but the CLI `--false-search-budget` remains the mechanical cap.

For communication experiments, use `--false-total-search-budget` to keep the
Python countermodel-search spend fixed across all rounds. Failed false hints now
emit:

- tried routes, such as `local_search:n=6:seed=0`;
- untried requested routes that were skipped because the slice ended;
- remaining fixed search budget;
- a compact `need_hint` request for the next LLM round.

After the first failed attempt, the LLM may copy exact route strings from
`untried_requested_routes` into a `routes` list. Those routes take priority over
the default size ordering, so the LLM can steer the next search precisely while
the total budget remains fixed.

The bounded propagation branch is exposed through `template:
"propagation"`/`"model_finder"` and routes such as `find_model:n5`. It is a
sidecar version of the larger solver's partial-table model finder, with extra
state for collaboration:

```json
{
  "kind": "false_model_hint",
  "template": "propagation",
  "routes": ["find_model:n5"],
  "focus_cells": [[0, 1], [4, 4]],
  "bias_cells": [{"cell": [0, 1], "values": [2, 3]}],
  "time_budget": 6
}
```

If propagation times out or hits a node cap, the next `CollaborationState`
includes `mechanical.false_search.propagation_runs`: node count, forced
assignments, conflicts, hot forced cells, blocked cells, branch cells, and the
best partial table profile. The same data is mirrored in `need_hint` as
`propagation_diagnostics`, so the LLM can choose a narrower route or focus/bias
the cells where the search actually branched.

## Useful Commands

Print a no-network prompt:

```bash
python3 scripts/llm_lean_sidecar.py --problem-id normal_0121 --dry-run
```

Verify a local candidate proof body:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id normal_0121 \
  --candidate-proof-file sidecar_runs/normal_0121_known_good.lean
```

Call an LLM with repair rounds:

```bash
zsh -lc 'python3 scripts/llm_lean_sidecar.py \
  --problem-id hard2_0107 \
  --config official-stage2/pipeline/results/llm_openrouter_fast_config.json \
  --rounds 3'
```

For direct OpenAI routing, pass a config or override the LLM fields:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id hard2_0107 \
  --base-url https://api.openai.com/v1 \
  --api-key-env OPENAI_API_KEY \
  --model <model-name>
```

Try the deterministic h-fact graph before any LLM call:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id normal_0121 \
  --pretry-h-graph \
  --no-llm
```

Ask the LLM for extra h-instantiation hints, not proof text:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id hard2_0107 \
  --mode hargs \
  --pretry-h-graph \
  --base-url https://api.openai.com/v1 \
  --api-key-env OPENAI_API_KEY \
  --model gpt-5.5 \
  --reasoning-effort low
```

Ask the LLM for a mechanically checked intermediate lemma:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id normal_0121 \
  --mode lemma_hint \
  --base-url https://api.openai.com/v1 \
  --api-key-env OPENAI_API_KEY \
  --model gpt-5.5 \
  --reasoning-effort low
```

Run the `gpt-oss-120b` rowconst handshake that solves `normal_0032`:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id normal_0032 \
  --mode lemma_hint \
  --rounds 3 \
  --config official-stage2/pipeline/results/llm_openrouter_fast_config.json \
  --max-h-facts 100 \
  --max-lemma-facts 160 \
  --congruence-depth 2 \
  --max-congruence-facts 1200 \
  --pretry-h-graph \
  --lemma-superposition-budget 20 \
  --midpoint-superposition-budget 30 \
  --standard-lemma-cert-budget 10
```

Replay a saved `lemma_hint` JSON without an LLM call:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id normal_0032 \
  --mode lemma_hint \
  --candidate-json-file /tmp/rowconst_hint.json \
  --rounds 1 \
  --standard-lemma-cert-budget 10
```

Replay a ranked lemma list without an LLM call:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id normal_0032 \
  --mode lemma_hint \
  --candidate-json-file /tmp/rowconst_candidates.json \
  --rounds 1 \
  --standard-lemma-cert-budget 10
```

Replay a square-witness chain without an LLM call:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id hard1_0018 \
  --mode lemma_chain \
  --candidate-json-file /tmp/square_chain_hint.json \
  --rounds 1
```

Ask `gpt-oss-120b` for the square-witness chain:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id hard1_0018 \
  --mode lemma_chain \
  --rounds 2 \
  --config official-stage2/pipeline/results/llm_openrouter_fast_config.json
```

The same command works for the related `hard3_0231` case; the live model returns
the four-lemma chain including `left_sandwich`.

Replay a false-side finite-model hint without an LLM call:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id hard2_0016 \
  --mode false_model_hint \
  --candidate-json-file sidecar_runs/false_hint_hard2_0016_broad_hint.json \
  --rounds 1 \
  --false-search-budget 12
```

Ask `gpt-oss-120b` for a false-side finite-model hint:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id hard2_0016 \
  --mode false_model_hint \
  --rounds 1 \
  --config official-stage2/pipeline/results/llm_openrouter_fast_config.json \
  --false-search-budget 18
```

Run a fixed-budget multi-round false-side experiment:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id hard2_0027 \
  --mode false_model_hint \
  --rounds 3 \
  --config official-stage2/pipeline/results/llm_openrouter_fast_config.json \
  --false-search-budget 6 \
  --false-total-search-budget 18
```

Replay `hargs` JSON without an LLM call:

```bash
python3 scripts/llm_lean_sidecar.py \
  --problem-id normal_0032 \
  --mode hargs \
  --candidate-json-file /tmp/hargs_smoke.json \
  --rounds 1
```

## Current Results

- `normal_0121` is accepted by the deterministic h-fact graph. Transcript:
  `sidecar_runs/hgraph_normal_0121_v1.jsonl`.
- `gpt-5.5` also solves `normal_0121` in one direct round from the exact h-fact
  menu. Transcript: `sidecar_runs/openai_gpt55_normal_0121_hfacts_v1.jsonl`.
- `gpt-5.5` produced a `lemma_hint` for `normal_0121` that the sidecar proved
  and used successfully. Transcript:
  `sidecar_runs/openai_gpt55_normal_0121_lemma_hint_v1.jsonl`.
- `normal_0032` is not solved by h-graph depth 2 plus a 20s goal-superposition
  pretry. Transcript:
  `sidecar_runs/autonomous_check_normal_0032_mechanical.jsonl`.
- `openai/gpt-oss-120b` via OpenRouter solves `normal_0032` in `lemma_hint`
  mode once the standard rowconst consumer is enabled. The first two rounds
  proposed the natural local bridge
  `y ◇ (z ◇ (y ◇ z)) = y ◇ ((y ◇ z) ◇ z)`, which the current mechanical side
  cannot prove. Round 2 proposed `a ◇ b = a ◇ c`; the explicit rowconst renderer
  produced a judge-accepted proof. Transcript:
  `sidecar_runs/autonomous_openrouter_normal_0032_lemma_hint_rowconst_v1.jsonl`.
- The same rowconst hint can be replayed locally with `--candidate-json-file`
  and no network call. Transcript:
  `sidecar_runs/autonomous_candidate_rowconst_normal_0032_v2.jsonl`.
- A ranked two-lemma replay ranks rowconst ahead of the larger local bridge and
  accepts without an LLM call. Transcript:
  `sidecar_runs/autonomous_candidate_multirowconst_normal_0032_v2.jsonl`.
- A proved-but-unused lemma replay now emits lifecycle plus instance diagnostics.
  Transcript:
  `sidecar_runs/autonomous_candidate_proved_unused_normal_0032_v1.jsonl`.
- `hargs` candidate JSON replay now runs locally and emits the normalized
  `SearchState`/`need_hint` contract. Transcript:
  `sidecar_runs/autonomous_candidate_hargs_normal_0032_v1.jsonl`.
- `gpt-5.4-mini` did not reliably assemble the same visible chain, which makes
  model strength a real bottleneck for proof planning.
- `hard2_0107` is now solved by the `right_square_chain` tool. The failed live
  repair run showed the model could follow inherited seed rows, but the
  single-lemma consumer could not prove the exact bridge. Mining the old failed
  proof revealed the helper chain `u ◇ (v ◇ v) = v` and `u ◇ v = v ◇ v`;
  rendering those helpers explicitly avoids disallowed `grind` axioms and closes
  the goal. Transcripts:
  `sidecar_runs/tool_call_right_square_chain_hard2_0107_v1.jsonl`,
  `sidecar_runs/tool_router_right_square_chain_hard2_0107_v1.jsonl`,
  `sidecar_runs/live_tool_call_hard2_0107_right_square_chain_v1.jsonl`.
- `hard3_0183` is now a live LLM-assisted solve. Mechanical baseline failed;
  `gpt-oss-120b` first proposed a local bridge that was plausible but not
  provable by current consumers, then after the explicit standard-helper prompt
  block proposed rowconst `a ◇ b = a ◇ c`. The square-rowconst renderer produced
  a judge-accepted proof. Transcripts:
  `sidecar_runs/balanced_openrouter_hard3_0183_helperblock_v1.jsonl`,
  `sidecar_runs/balanced_candidate_hard3_0183_rowconst_v1.jsonl`.
- `hard1_0018` is now solved by the new square-witness `lemma_chain` interface.
  The hand-proof chain is: all squares are equal; a square acts as a right
  identity; `(v ◇ u) ◇ v = u`; then the goal RHS reduces to `x`. A replay of
  the chain is accepted, and `openai/gpt-oss-120b` via OpenRouter returns the
  exact chain in round 0. Transcripts:
  `sidecar_runs/lemma_chain_hard1_0018_replay_v4.jsonl`,
  `sidecar_runs/live_openrouter_hard1_0018_lemma_chain_v1.jsonl`.
- `hard1_0018` can also be solved from a single `lemma_hint` naming the
  sandwich lemma when `--standard-lemma-cert-budget` is enabled. Transcript:
  `sidecar_runs/lemma_hint_sandwich_hard1_0018_replay_v2.jsonl`.
- `hard3_0231` has the same hypothesis as `hard1_0018` and is now solved by the
  generalized square-witness chain. The extra derived rule is
  `v ◇ (u ◇ v) = u`, which reduces `x ◇ (y ◇ x)` to `y`; then the RHS reduces
  through a square and the old sandwich rule. A three-lemma replay works because
  the sidecar derives `left_sandwich`; a four-lemma replay and a live
  `gpt-oss-120b` run also accept. Transcripts:
  `sidecar_runs/lemma_chain_hard3_0231_replay_v3.jsonl`,
  `sidecar_runs/lemma_chain4_hard3_0231_replay_v1.jsonl`,
  `sidecar_runs/live_openrouter_hard3_0231_lemma_chain_v1.jsonl`.
- `hard2_0016` is now a false-side LLM-mechanical win. A live
  `openai/gpt-oss-120b` run proposed a compact `local_search` hint over sizes
  `[5, 6, 7]` and seeds `[0, 1, 2]`; the sidecar found a size-6 countermodel and
  emitted a judge-accepted `decideFin!` certificate under the model's requested
  18s search budget. Replays:
  `sidecar_runs/false_hint_hard2_0016_local_search_v3.jsonl`,
  `sidecar_runs/false_hint_hard2_0016_broad_local_search_v3.jsonl`; current-code
  live run: `sidecar_runs/live_openrouter_hard2_0016_false_hint_v8_round2.jsonl`.
- With a 12s mechanical cap, the broad replay can accept but the live run is
  still flaky because local repair may miss all attempted seeds. Failed capped
  live transcript: `sidecar_runs/live_openrouter_hard2_0016_false_hint_v5.jsonl`.
- The same broad hint does not solve `hard2_0093` in a 12s replay. Transcript:
  `sidecar_runs/false_hint_hard2_0093_broad_local_search_v1.jsonl`. That case
  likely needs either a better structural template or a longer/targeted model
  search strategy.
- Fixed-budget false-side sweep, using 18s total Python search per problem
  split into 6s per hint over three LLM rounds:
  `hard2_0016` accepts in round 0 from a broad local-search hint, spending
  3.238s of search. `hard1_0009`, `hard2_0125`, and `hard2_0027` do not solve
  under the same cap. The useful signal is that the LLM adapts: for example,
  `hard2_0027` copies exact `untried_requested_routes` in round 1, then switches
  to `model_finder` in round 2. Transcripts:
  `sidecar_runs/fixed_budget_live_hard1_0009_v1.jsonl`,
  `sidecar_runs/fixed_budget_live_hard2_0016_v1.jsonl`,
  `sidecar_runs/fixed_budget_live_hard2_0125_v2_routes.jsonl`,
  `sidecar_runs/fixed_budget_live_hard2_0027_v3_routes.jsonl`.
- `CollaborationState` smoke tests:
  `sidecar_runs/collab_state_false_smoke_v1.jsonl` records a failed false hint
  with tried/untried routes and budget state; `sidecar_runs/collab_state_true_chain_smoke_v1.jsonl`
  records an accepted square-witness chain with helper normal forms.
- False diagnostic smoke tests:
  `sidecar_runs/false_diag_hard2_0027_smoke_v1.jsonl` shows an H-satisfying
  near-model where G still holds, so the next hint should be G-breaking.
  `sidecar_runs/false_diag_hard2_0016_broad_v2.jsonl` preserves the known
  `hard2_0016` solve and records a near-model with only two H violations while
  G already fails on many assignments.
- Focused false-consumer smoke tests:
  `sidecar_runs/focused_hint_hard2_0016_hotspots_v1.jsonl` verifies that
  `focused_local_search` consumes H-hotspot `focus_cells` and reports the next
  hotspot set. `sidecar_runs/focused_hint_hard2_0027_gbreak_v2.jsonl` verifies
  the G-breaking focused path, though it does not solve that case. The broad
  `hard2_0016` regression still accepts after these changes:
  `sidecar_runs/focused_regression_hard2_0016_broad_v2.jsonl`.
- Propagation/model-finder smoke tests:
  `sidecar_runs/propagation_hint_normal_0003_route_n2_v1.jsonl` accepts from
  exact route `find_model:n2` and checks the generated finite countermodel in
  Lean.
  `sidecar_runs/propagation_hint_hard2_0027_n5_v2.jsonl` does not solve within a
  3s cap, but records useful propagation diagnostics: 794 nodes, 298 forced
  assignments, 628 conflicts, and hot branch/blocked cells for the next hint.
  `sidecar_runs/propagation_regression_hard2_0016_broad_v2.jsonl` confirms the
  broad local-search false path still accepts.
- Fixed-budget propagation/LLM sweep:
  seeded `find_model:n5` runs on `hard1_0009`, `hard2_0093`, `hard2_0125`, and
  `hard2_0027` did not solve under an 8s total search cap. The LLM noticed the
  propagation diagnostics, but usually spent the next real budget on broad or
  lightly-focused local search. `hard2_0016` remains the useful control:
  `sidecar_runs/propagation_softprompt_live_hard2_0016_v2.jsonl` accepts after a
  propagation seed, via local search at size 6. A stricter protocol-rejection
  experiment conserved budget but harmed this control, so it was not kept as
  default behavior.

## Next Rungs

The next high-return additions should stay narrow and verified:

1. Add more explicit standard-lemma renderers when we see repeated LLM hints
   that are semantically right but rejected by `grind`.
2. Look for another pair of related failures where one proof family can be
   opened by adding a small derived rule to an existing verified chain.
3. For false cases, run a fixed-budget sweep over hard failures and compare
   whether the LLM uses `propagation_runs` to choose better routes, focus cells,
   or bias cells.
4. Keep false-side development on a fixed search budget while strengthening the
   mechanical consumers for the hints the LLM already knows how to express.
5. Let `lemma_hint` ask for a second rung only after a promising lemma is proved
   or recognized but cannot close the goal.
6. Surface richer mechanical state from superposition: target, budget, whether
   no derivation was produced or produced bodies failed Lean, and a compact
   proof-obligation summary.
7. Build a structured success/failure corpus from transcripts, then use it for
   few-shot retrieval.

## Current Scope

The sidecar now has both wings, but deliberately in narrow forms. On true cases,
it learns whether LLMs can propose small lemma chains that the mechanical
renderer proves and stitches. On false cases, it learns whether LLMs can steer
finite countermodel search through carrier sizes, routes, focus cells, bias
cells, and propagation diagnostics. The aim is still collaboration quality, not
maximum standalone mechanical coverage.
