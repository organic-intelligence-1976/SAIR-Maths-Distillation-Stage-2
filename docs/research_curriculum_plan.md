# Research-First System 1 / System 2 Curriculum Plan

Status: active; first four vertical slices implemented and measured, 2026-07-17

This document reframes the collaborative solver work as a research program in
verified LLM/mechanical mathematical reasoning. The SAIR Stage 2 competition is
an important proving ground and a source of constraints, data, and feedback, but
competition score is not the primary objective.

The central research question is:

> Can an untrusted LLM strategist learn to reconstruct, compose, improve, and
> eventually invent mechanically verified mathematical capabilities, rather
> than merely select from a fixed portfolio?

The project should deliberately create attainable capability frontiers for
System 2. It should sometimes withhold mature end-to-end mechanical solutions
while preserving exact compositional primitives. Once System 2 reliably
reconstructs a withheld capability, that capability returns to the full system
and the curriculum frontier moves upward.

The intended flywheel is:

```text
withhold a completed capability
-> expose strong generic primitives and structured failure state
-> let System 2 plan, propose, and repair
-> mechanically verify every contribution
-> test transfer and composition
-> distill the verified discovery into memory, policy, or a new tool
-> restore it to the full system
-> raise the frontier
```

The final system is not meant to have weak mechanics. Controlled mechanical
weakness is a development instrument, not a deployment architecture.

## 0. Implementation Checkpoint: Vertical Slices 1 and 2

The first slice is now implemented in `baby_solver.py` and
`scripts/midpoint_curriculum_probe.py`. It deliberately changes only two
execution seams instead of refactoring the packed solver:

- an audited semantic registry currently contains two regression fixtures:
  the Austin implication E1167 -> E1763 and the open finite implication
  E677 -> E255;
- semantic state now carries `semantic_target`, `general_status`,
  `finite_status`, `certificate_class`, competition-policy information, and
  the current solver's artifact support;
- every finite-model route has a semantic stop guard;
- `hard2_0027` blocks finite countermodel search and routes first to the
  infinite-model artifact protocol instead of spending compute on finite
  searches that cannot succeed;
- a remaining `semantic_solver_capability_gap` is explicitly an artifact
  construction gap, not a judge limitation: the current Lean false goal can
  express an infinite Type-level model, while finite tables cannot solve this
  semantic class;
- the existing tool registry now exposes capability IDs, primitive
  dependencies, a manifest, and experimental masks;
- the right-square curriculum family can run full mechanics, a focused-tool
  dropout with the generic midpoint prover available, and a negative control
  with both routes withheld.

### Measured result

The first paired case was `right_square_train_hard2_0107`:

| Mode | Result | Official Lean judge |
|---|---|---|
| full `right_square_chain` | proof body built | accepted |
| focused shortcut withheld | blocked by mask | not invoked |
| shortcut withheld, generic `lemma_chain` available | proof body built | accepted |
| shortcut and generic midpoint prover withheld | no proof body | not invoked |

All four attribution checks passed. The complete case, including repeated
official-judge calls, took about 18.1 seconds locally. The Austin semantic stop
took less than 0.2 milliseconds. An ordinary five-problem competition-path
regression still solved 5/5 in about 83 seconds.

This result establishes that the intervention mechanism works and that a
known generic lemma chain can compensate for a withheld completed renderer. It
does **not** yet establish that a live LLM can discover that chain. That is the
next empirical threshold.

### Practical effort observed

This slice changed roughly 500 lines (about 480 net new lines) across the two execution files,
plus this plan and generated evidence. Most of the effort was not the mask
itself; it was making semantic status, composite capability dependencies,
negative controls, and attribution explicit enough that the result cannot be
mistaken for ordinary tool routing.

Machine-readable evidence is in
`.artifacts/research_curriculum_vertical_slice_v1.json`; its compact companion
is `.artifacts/research_curriculum_vertical_slice_v1.md`.

### Vertical Slice 2 evidence

The second bounded slice completed the core targets left by Vertical Slice 1:

1. `scripts/update_semantic_registry.py` generated a source-stamped registry of
   all 820 Austin implications from Equational Theories Project commit
   `df8184f8ae59c71d6f5463b71682d871823a779c`. The source file hash is recorded
   in `data/semantics/austin_implications.json`. An audit of all 1,669 public
   rows found exactly one Austin implication, `hard2_0027`.
2. A policy-sensitive `infinite_model_artifact` action now has an explicit
   capability contract and Lean trust boundary. The closed historical
   E3994 -> E3588 countermodel is accepted by the official judge under the
   research declaration policy. The unchanged competition declaration
   allowlist rejects that implementation because it reaches disallowed
   declarations; this is a deployability restriction, not a mathematical
   refutation.
3. The live right-square alpha-renaming probe initially failed in three repair
   rounds. It proposed a false target-specific lemma, repeated it, and then
   proposed two false lemmas. The small-model filter correctly refuted these
   candidates.
4. On the different `square_sandwich` family holdout, the live model first
   discovered two correct universal lemmas. The generic prover proved them but
   could not consume the goal. The next LLM turn discarded this partial
   progress. This exposed a missing protocol invariant: verified lemmas must be
   retained while a plan is extended.
5. After adding explicit alpha-invariance, decisive-countermodel, and monotone
   partial-progress rules, the live model returned the full four-lemma
   square-sandwich chain. A later capability-boundary audit found that the
   generic consumer silently invoked its internal focused square-sandwich
   fallback. This apparent recovery is therefore invalid as dropout evidence;
   it is retained as an example of why capability interventions must cover
   internal fallback edges, not only registry entry points.
6. With that protocol frozen, a fresh second alpha-renaming of the right-square
   case succeeded on the first live response under the same paired intervention
   and Lean check.

The main machine-readable records are:

- `.artifacts/public_semantic_audit_v2.json`;
- `.artifacts/infinite_model_probe_v2.json`;
- `.artifacts/research_curriculum_square_holdout_live_v4.json` (instructive
  failure with two proved lemmas discarded);
- `.artifacts/research_curriculum_square_development_live_v5.json` (superseded
  apparent success; later shown to use a masked internal focused fallback);
- `.artifacts/research_curriculum_right_square_frozen_live_v6.json` (fresh
  alpha-renaming success under the frozen protocol).

### What the new evidence changes

The long-term thesis survives, but the near-term unit of research changes. A
single LLM lemma proposal is too brittle. The primary object should be a
**verified, stateful repair loop**:

```text
propose a plan node
-> prove or refute it mechanically
-> add proved nodes permanently to trusted episode state
-> attach concrete countermodels or proof-search frontiers to failed nodes
-> ask System 2 to extend or revise only the unverified part
-> verify the composed plan
```

The current successes are proof of protocol feasibility, not yet proof of
general mathematical learning. The square-sandwich target became a development
case once its failure shaped the prompt. The fresh right-square result tests
alpha-renaming transfer, but it has the same mathematical structure as its
training example. Neither result establishes cross-family abstraction,
composition, or novel lemma invention. Those claims now require frozen prompts,
predeclared splits, repeated trials, and cases whose winning helper schemas are
not copied verbatim into the training text.

### Vertical Slice 3: first-class repair state and a corrected boundary

The third slice moved monotone progress from prompt advice into executable
episode state:

1. `curriculum_blackboard.py` canonicalizes universal equations up to variable
   renaming and equality reversal. Mechanically proved nodes are immutable;
   small-model-refuted nodes are blocked under the same canonical signature;
   merely unproved nodes are neither trusted nor declared false.
2. New LLM lemma proposals are automatically composed with every trusted node
   before the generic prover runs. The LLM can therefore propose only the
   missing part of a plan without accidentally deleting earlier verified work.
3. Capability masks now propagate into the internal focused fallbacks of the
   generic midpoint consumer. Replaying square-sandwich after this correction
   shows that the known four-lemma payload does **not** close the held-out goal
   with the focused renderer disabled. The earlier square-sandwich attribution
   is superseded.
4. A deterministic right-square probe begins with one proved-but-insufficient
   helper, asks for only the second helper, merges both on the blackboard, and
   closes the goal through the generic prover. Lean accepts the result; the
   negative control removes it. The same probe records a small-model-refuted
   conjecture and blocks an alpha-renamed repetition before another prover call.
5. Live artifacts now record a development/sealed/postmortem label, public LLM
   settings, config and code hashes, capability-manifest hash, and per-round
   prompt hashes. The adapter also normalizes the common
   `{"lemma_chain": [...]}` response envelope.
6. A one-trial, no-few-shot development ablation did not solve the right-square
   target in either stateful or stateless mode. The stateful arm accumulated
   four distinct decisive refutations but never found a proved node, so there
   was no positive partial progress for retention to exploit. This is useful
   negative evidence, not a rate estimate.

The decisive artifact is `.artifacts/lemma_blackboard_probe_v8.json`. The two
live development arms are `.artifacts/right_square_stateless_no_fewshot_v10.json`
and `.artifacts/right_square_stateful_no_fewshot_v10.json`.

This changes the next benchmark design: it must contain explicit
**partial-progress continuation episodes** as well as solve-from-scratch
episodes. Otherwise an experiment mostly measures initial lemma invention and
cannot identify the value of stateful verified repair.

### Vertical Slice 4: executable modular walking skeleton

The high-level research architecture now exists as working modules under
`research_system/`, with stable contracts for protocol records, semantics,
capability policy, planning, blackboard state, mechanical execution, official
verification, curriculum construction, orchestration, experience, distillation,
evaluation, integration, and competition compilation.

The first end-to-end modular run passed three reference lanes:

- a right-square true proof reconstructed from two separately proposed helpers
  with the focused tool withheld, accepted by Lean, with its full baseline and
  negative control behaving correctly;
- a size-2 finite countermodel accepted by Lean;
- the E3994 -> E3588 infinite countermodel accepted under the research policy.

Five attributed episodes were stored, four were accepted, and the distiller
created verified `proof_plan_schema`, `model_instance`, and
`infinite_model_artifact` records. The generated competition snapshot was
333,482 bytes, satisfied the single-file/AST/PROMPT/size contract, and passed an
official proxy/judge protocol smoke with zero LLM calls and one accepted judge
call.

The v1 compiler still treats `baby_solver.py` as one legacy packed source unit.
It records policy-sensitive definitions explicitly. Physical tree shaking is a
later compiler improvement, not a claim of the current build.

Architecture, commands, evidence paths, and component status are documented in
`docs/research_system_architecture.md`.

### Vertical Slice 5: live state, resume, and verified branching

The modular runtime now invokes a live OpenAI-compatible System-2 planner. Its
turn context contains the capability manifest, a bounded mathematical summary
of worker feedback, trusted/refuted blackboard nodes, and optional verified
artifacts. It no longer sends an unbounded raw prover state.

Verified partial thought now persists across sessions. A resumed episode loads
only mechanically proved and small-model-refuted nodes, restores the last
compact observations, and records its parent episode. The LLM can also return a
small batch of candidate helpers in one `lemma_chain`; refuted repetitions are
removed individually and every mechanically proved candidate survives.

Development runs on the right-square dropout have not yet solved the clean
live task, but they now accumulate useful state instead of producing disposable
failures. Across the clean, partial-continuation, and branching runs, the loop
retained several nontrivial universal lemmas and decisive refutations. This is
the intended substrate for curriculum learning. The exposed bottleneck is now
mathematical abstraction: the model tends to copy local closest-pair equations
instead of extracting a smaller reusable law.

## 1. Project Priorities

The priorities, in order, are:

1. Develop general System 2 capabilities: representation choice, decomposition,
   lemma invention, model-family invention, repair, budget allocation, tool
   composition, and reusable abstraction.
2. Preserve a sound, exact mechanical substrate and Lean verification boundary.
3. Demonstrate transfer to unseen equation families and larger-order laws.
4. Use the system to attack stubborn low-order and order-5 mathematical cases,
   including cases beyond current mechanical coverage.
5. Maintain a competitive full-strength SAIR submission as an integration test
   and source of realistic constraints.

The following are explicitly not primary goals:

- maximizing the current public-set score by embedding every known answer;
- keeping System 1 weak after a capability has been learned;
- moving hard-coded strategy tables from Python into the prompt;
- trusting LLM mathematical claims without independent checking;
- labeling an LLM-routed invocation as a new capability without a
  counterfactual comparison;
- optimizing only for order <= 5.

## 2. Competition Semantics: Finite Versus General Magmas

This distinction must become a first-class field in every problem and
experiment.

### 2.1 What the official materials currently say

The mathematical task is stated as implication over every magma. A true
certificate therefore proves:

```text
for every magma G, H(G) -> Goal(G)
```

The official Stage 2 prose says that a false certificate is a **finite magma
witness**. This wording appears in both the competition overview and evaluation
rules.

However, the current public Lean judge constructs the false goal as:

```lean
exists (G : Type) (_ : Magma G), EquationLHS G ∧ not EquationRHS G
```

It does not require `Finite G`, `Fintype G`, or `G = Fin n`. Thus the executable
judge currently accepts an arbitrary Type-0 countermodel if it satisfies the
proof policy.

The public practice distribution exposes the mismatch. `hard2_0027` is
Equation 1167 -> Equation 1763. The Equational Theories Project records this
implication as true for all finite magmas but false in general. Consequently:

- no finite table can solve `hard2_0027`;
- an infinite countermodel is mathematically required;
- the current judge goal is broad enough to express such a certificate;
- the official prose still says that a false certificate should be finite.

The private Stage 2 set is still TBD, so it is not currently possible to assume
that all false evaluation rows have finite witnesses.

### 2.2 Operational policy for this project

Every problem record and search state should carry:

```json
{
  "semantic_target": "general_implication | finite_implication",
  "general_status": "true | false | unknown",
  "finite_status": "true | false | unknown",
  "certificate_class": "general_proof | finite_model | infinite_model | unknown",
  "competition_policy": "prose_finite | judge_general"
}
```

The solver should use a finite-first search policy without conflating it with
finite-only semantics:

1. Try cheap finite witnesses because they are compact and easy to verify.
2. Stop all finite countermodel search when a trusted finite implication is
   known.
3. Route general-false/finite-true pairs to an infinite-model lane.
4. Keep finite implication research, general implication research, and
   competition certificate policy separate in reports.
5. Add a configuration switch that can enforce either the prose contract or the
   current executable judge contract.

Before relying on an infinite certificate in a competition submission, ask SAIR
to clarify whether the finite wording is normative or whether the formal goal
is intentionally broader. The research system should support both regardless.

### 2.3 Immediate correction to existing project state

Existing notes that diagnose `hard2_0027` as insufficient finite-model reach
are obsolete. Its failed size-2 through size-9 searches remain useful as
historical evidence about the protocol, but not as evidence about the required
mathematics. Future reports must identify it as a semantic classification
failure and an infinite-model curriculum case.

### 2.4 2026-07-27 resolution

`hard2_0027` now has an official-judge-accepted infinite certificate. It uses
a modified parity walk on `Nat`, traced to the dual of the Equational Theories
Project's `Equation1659_facts`. The readable certificate and structured plan
are:

- `data/semantics/hard2_0027_modified_parity_model.lean`;
- `data/semantics/hard2_0027_modified_parity_model_plan.json`.

The packed solver keeps a compressed copy because the submission contract is
single-file. This is attributed as verified symbolic-memory replay, not as an
LLM discovery.

The structured contract now has six parts: carrier, pre-model definitions,
operation, setup lemmas, universal H proof, and concrete not-G proof. It also
supports indexed component patches and complete active-plan handoff between
LLM rounds. A separate accepted `Fin 257` probe confirms that formula-defined
finite models do not require an explicit operation table.

## 3. Research Clues From the Published Work

The research plan should be grounded in what the Equational Theories Project
actually found difficult and in the few places where AI contributed something
qualitatively new.

### 3.1 The bounded order <= 4 universe is solved in general, not exhausted as research

The ETP determined all 22,028,942 directed implications among the 4,694 laws of
order <= 4 under general magma semantics, with Lean-verified proofs or
refutations. This makes the order <= 4 corpus an unusually valuable teacher and
evaluation environment:

- ground truth is comprehensive;
- proof and model artifacts exist;
- hard cases and failed historical approaches are documented;
- general and finite implication can differ;
- one can create artificial frontiers without guessing the answer.

It should be treated as a curriculum laboratory, not merely a benchmark to
memorize.

### 3.2 There is a genuine unresolved low-order finite implication

The ETP paper and current blueprint identify

```text
E677 |=_fin E255
```

as the last unresolved finite implication among the order <= 4 laws, up to
duality. General implication is already false: the blueprint constructs the
free 677 magma and shows that it does not satisfy E255. The remaining question
is whether every finite 677 magma satisfies E255.

This is an excellent long-term research moonshot because it requires:

- explicit finite reasoning rather than ordinary equational consequence;
- use of injectivity/surjectivity consequences of finiteness;
- structural lemma invention;
- integration of partial human mathematics with search;
- either a new finite countermodel or a finite-only theorem.

It is not an appropriate first curriculum exercise. The system should earn its
way to this case through transfer and representation-change milestones.

### 3.3 Order 5 contains real classification frontiers

The official Stage 2 law file contains 62,576 laws of order <= 5: the 4,694
lower-order laws plus 57,882 laws of exact order 5.

The ETP order-5 Austin-law study currently reports:

- 19,392 exact-order-5 laws known to admit only trivial models;
- 38,360 with known nontrivial finite models;
- 106 with only trivial finite models known;
- among those 106, 10 proven Austin laws with nontrivial infinite models;
- for the other 96, nontrivial infinite-model existence remains unknown;
- 24 further laws whose nontrivial finite-model status remains unknown;
- some minimum known finite models at sizes around 17, with one size-26 model
  whose minimality was not exhaustively established.

These categories offer a graded research suite:

1. reproduce known small finite models;
2. rediscover known large or structured finite models;
3. distinguish finite-trivial laws from Austin laws;
4. reconstruct known infinite models;
5. attack one of the 96 unknown infinite-model cases;
6. attack one of the 24 unknown finite-model cases.

Equation 5093 is another explicit open direction: it has no nontrivial finite
models, while the existence of an infinite model remains open.

### 3.4 The most relevant historical LLM success was theory invention

The ETP reports that existing automated theorem provers were generally more
effective than the publicly available LLMs on difficult implications. This is
important negative evidence and should not be hidden.

But it also reports one result that strongly supports this project's thesis:
ChatGPT guessed a complete rewriting system for Equation 3523; the system was
then formally verified and resolved all implications from that law.

That is the desired System 2 role:

- not manually enumerating thousands of rewrites;
- not returning an unverified proof blob;
- but proposing a new representation-level artifact that changes the entire
  mechanical search landscape.

Reproducing this type of discovery under controlled conditions should be an
early research milestone.

### 3.5 Tool orchestration is a real mathematical problem

The ETP found significant complementarity between theorem provers, large
performance changes from parameter settings and formula order, and hard cases
that changed from hours to fractions of a second after the right configuration
was found. This supports LLM-guided orchestration, but it also supplies a strong
baseline: learned or deterministic portfolio schedulers may solve part of the
same problem without language reasoning.

System 2 should therefore be compared against:

- fixed schedules;
- empirical cost profiles;
- bandit-style allocation;
- oracle schedules derived after the fact.

Its distinctive target is representation change and artifact invention, not
merely scheduling where a statistical controller is sufficient.

### 3.6 Distillation must be an explicit learning loop

The SAIR challenge is inspired by work on distilling many-shot demonstrations
into compact cheat sheets. The lesson for this project is broader than prompt
compression: successful episodes must become reusable, inspectable artifacts.

A fixed LLM does not improve because it was tested repeatedly. Improvement must
occur through one or more of:

- validated strategy memory;
- retrieval over proof and failure abstractions;
- a learned controller;
- prompt/cheat-sheet distillation;
- fine-tuning on verified trajectories;
- compilation of discoveries into new mechanical tools.

## 4. Non-Negotiable Design Principles

### 4.1 Two lanes, always

Maintain two continuously runnable systems:

**Full-strength reference lane**

- all available mechanical capabilities enabled;
- establishes the actual solver frontier;
- acts as teacher, oracle, and regression baseline;
- can be packed for competition submission.

**Curriculum lane**

- selected completed capabilities are withheld by configuration;
- generic exact primitives remain enabled;
- each run declares the skill being exercised;
- transfer and reintegration matter more than raw solve count.

Never delete or weaken the full-strength reference in order to create a
curriculum frontier.

### 4.2 Withhold solutions, not hands and eyes

Always retain:

- parsing, canonicalization, matching, and unification;
- exact substitution and contextual rewriting;
- term indexing and equality data structures;
- finite-table evaluation and constraint checking;
- proof-trace rendering;
- Lean and model verification;
- structured progress and failure telemetry.

Candidate capabilities to withhold include:

- a specialized chain renderer;
- a direct model-bank hit;
- a problem-ID lookup;
- a hard-coded strategy card revealing the route;
- a monolithic fallback solver;
- an end-to-end completion configuration known to solve the case.

### 4.3 Capability dropout, not one permanently crippled solver

Withholding must be configuration-driven and preferably randomized across
research episodes. The controller should see an explicit capability manifest,
not silently encounter missing functions.

Example:

```json
{
  "episode_id": "...",
  "learning_target": "multi_lemma_decomposition",
  "available_capabilities": [
    "parse",
    "unify",
    "bounded_egraph",
    "prove_proposed_lemma",
    "lean_verify"
  ],
  "withheld_capabilities": [
    "right_square_chain_renderer"
  ]
}
```

Varying the withheld capability prevents the LLM from overfitting to one fixed
artificial weakness and directly tests adaptation to tool availability.

### 4.4 Soundness remains mechanical

Every accepted mathematical artifact must be independently checked:

- Lean for general true implications and formal model constructions;
- exhaustive table evaluation for finite countermodels before Lean rendering;
- proof-producing completion/equality saturation where feasible;
- explicit validation obligations for rewrite systems, invariants, and model
  families.

The LLM may be creative precisely because it is never trusted.

### 4.5 Curriculum parity is a milestone, not the final claim

The capability progression is:

```text
recovery
-> transfer
-> composition
-> abstraction
-> invention
-> full-system integration gain
```

Recovering a deliberately withheld known solution is useful. It should be
reported as `curriculum_recovery`, not as unique new coverage.

## 5. Target System Architecture

The current code already contains many required pieces, but they are mixed into
a packed competition-oriented file and a larger sidecar. The transition should
be incremental.

### 5.1 Blackboard state

Replace prompt-sized narrative state with a versioned blackboard:

```json
{
  "problem": {},
  "semantics": {},
  "budget": {
    "wall_seconds_remaining": 0,
    "llm_tokens_remaining": 0,
    "judge_calls_remaining": 0
  },
  "capabilities": {
    "available": [],
    "withheld": [],
    "learning_target": ""
  },
  "proof_plan": {
    "nodes": [],
    "edges": [],
    "open_obligations": []
  },
  "facts": {
    "proved_equations": [],
    "refuted_equations": [],
    "candidate_invariants": []
  },
  "search": {
    "attempts": [],
    "frontiers": [],
    "exhausted_routes": [],
    "semantic_obstructions": []
  },
  "memory": {
    "retrieved_artifacts": [],
    "candidate_new_artifacts": []
  }
}
```

Mechanical tools write structured observations. System 2 proposes state
transitions. The adapter validates actions. The verifier alone promotes claims
to proved facts.

### 5.2 Expanded System 2 action language

Protocol v0 mainly supports tool calls, midpoints, lemma chains, proof bodies,
and finite tables. Protocol v1 should add:

```text
propose_lemma
propose_lemma_dag
choose_representation
orient_rewrite_rules
propose_model_family
propose_invariant
propose_finite_only_argument
request_bounded_search
synthesize_workflow
generalize_verified_artifact
retire_route
```

Each action must create concrete mechanical obligations. For example, a
proposed rewrite system creates obligations for soundness, useful normalization,
and, where claimed, termination or confluence.

### 5.3 Trusted mechanical workers

The long-term worker portfolio should include:

- proof-producing equality saturation;
- ordered completion and superposition;
- assumption-aware goal search;
- finite-model CSP/model construction;
- symbolic affine and polynomial model analysis;
- infinite construction templates;
- invariant checking;
- Lean proof and model rendering;
- artifact minimization.

These are not competitors to System 2. They are the exact substrate that makes
high-level strategy useful.

### 5.4 Experience and distillation store

Every serious episode should produce a structured record:

```json
{
  "problem_signature": {},
  "capability_mask": {},
  "controller_actions": [],
  "mechanical_observations": [],
  "verified_artifacts": [],
  "failed_conjectures": [],
  "cost": {},
  "counterfactual_results": {},
  "distillation_candidate": {}
}
```

Raw transcripts may be retained for debugging, but retrieval should use
canonical mathematical summaries rather than entire conversations.

### 5.5 Development source versus packed artifact

`baby_solver.py` should remain a reproducible packed baseline during the first
curriculum phases. New research architecture should develop modularly, with a
later build step producing a single-file solver. This avoids maintaining a
research system by repeatedly editing a 6,000-line packed artifact.

## 6. Curriculum Ladder

Each level has a training environment, held-out test, and graduation gate.

### Level 0: Measurement and capability masks

Goal: make artificial frontiers scientifically interpretable.

Build:

- a capability manifest for every tool and specialized renderer;
- configuration-driven capability dropout;
- paired full-strength and handicapped runs;
- corrected attribution categories;
- semantic finite/general classification.

Graduation gate:

- the same problem can be replayed with a declared capability mask;
- reports identify exactly what was withheld;
- full-strength results remain unchanged;
- no route is called load-bearing without a paired counterfactual.

### Level 1: Routing under changing tool availability

Goal: select a suitable existing worker while respecting cost and exclusions.

Exercises:

- vary which tools are available;
- rename non-semantic tool identifiers while preserving descriptions;
- include plausible but inapplicable tools;
- require explicit stop decisions after semantic impossibility evidence;
- compare against a fixed scheduler and cost-profile scheduler.

Graduation gate:

- reliable selection on held-out problem families;
- no dependence on public problem IDs;
- improvement over the deterministic scheduler on at least one heterogeneous
  fixed-budget suite;
- correct avoidance of finite search on known finite-true/general-false pairs.

### Level 2: Parameterization and budget metareasoning

Goal: configure workers and allocate shared compute rather than merely naming a
tool.

Implementation seed (2026-07-18): `RenewableBudgetBroker` now assigns initial
and renewable geometric leases to separate midpoint attain/consume legs. The
policy is a bounded JSON genotype, every decision is logged, and mutation plus
scoreboard scripts support fixed-suite selection. See
`docs/budget_broker_v1.md`. This is the first within-action allocator; the
remaining Level-2 work is cross-worker allocation and learned value estimates.

Exercises:

- select search depth, term weight, model size, seed, and goal assignment;
- decide between several short probes and one deep run;
- interpret progress curves and timeouts;
- update route value after negative evidence;
- choose when an LLM call is worth more than additional mechanical search.

Graduation gate:

- lower regret than fixed schedules on held-out mixed suites;
- fewer repeated exhausted calls;
- calibrated stop/escalate decisions;
- accepted-count-versus-total-compute improves, not only final coverage.

### Level 3: Lemma and proof-plan decomposition

Goal: reconstruct withheld proof families using generic proving primitives.

The existing `midpoint_curriculum_probe.py` is the seed of this level. Extend it
from a fixed set of known-good chains into a general capability-dropout runner.

Exercises:

- hide right-square, square-sandwich, projection-pair, rowconst/opconst, and
  related focused renderers;
- retain generic universal-equation proving and Lean checking;
- ask System 2 for reusable lemmas, not the goal restated as a midpoint;
- represent plans as DAGs rather than one flat chain;
- return proof-node-specific failures;
- test alpha-renamed, dual, syntactically disguised, and larger-order variants.

Graduation gate:

- recovery across a predeclared suite of existing curriculum families, with
  success rates reported over repeated live trials;
- transfer to sealed held-out members not used for prompt or protocol tuning;
- at least one held-out helper schema not present verbatim in the few-shot text;
- successful composition of two families demonstrated only separately;
- at least one verified non-hardcoded intermediate lemma that improves a
  previously failing generic proof search.

### Level 4: Representation change and model-family invention

Goal: decide that the current proof/search language is wrong and propose a more
useful one.

Exercises:

- finite versus infinite model classification;
- affine/linear magma hypotheses;
- twisting, quotient, product, and piecewise constructions;
- invariant and canonizer proposals;
- candidate normal forms and rewrite orientations;
- finite-only reasoning using injectivity/surjectivity equivalence;
- detection that a search family is mathematically impossible.

Graduation gate:

- correctly reclassify `hard2_0027` without finite search;
- reconstruct at least one known infinite countermodel family;
- rediscover a known structured finite model that naive local search misses;
- produce one useful representation-level artifact verified independently.

### Level 5: Tool and workflow synthesis

Goal: compose generic primitives into a reusable procedure absent from the
fixed tool registry.

Exercises:

- synthesize a finite-model workflow from goal assignments, propagation,
  symmetry breaking, and checking;
- assemble a staged proof search from lemma proposal, bounded saturation, and
  repair;
- define a new derived operation or abbreviation that changes prover behavior;
- output an executable workflow specification, not unrestricted code at first.

Graduation gate:

- the synthesized workflow solves multiple held-out cases;
- the workflow is mechanically validated and budget bounded;
- compiling it into System 1 improves the full-strength system;
- the controller can explain when the workflow is applicable and when it is
  not.

### Level 6: Library formation and Marathon transfer

Goal: make discoveries compound across a batch.

Exercises:

- decide which proved lemmas deserve canonical library entries;
- minimize and generalize proof fragments;
- retrieve by structural signature rather than problem ID;
- reuse models as refutation filters;
- learn from failed conjectures without poisoning trusted state;
- compare no-memory, raw-memory, and distilled-memory variants.

Graduation gate:

- a discovery from an earlier problem reduces cost or enables a later solve;
- verified transfer survives variable renaming and duality;
- the distilled store beats raw transcript retrieval at equal context budget;
- full-strength Marathon performance improves.

### Level 7: Mathematical research frontiers

Goal: contribute genuinely new mathematics or a new verified computational
classification.

Candidate ladder:

1. Reproduce the E3523 complete-rewriting-system discovery from weak initial
   guidance and verify the resulting system.
2. Recover known order-5 Austin infinite models from structural hints.
3. Classify selected known order-5 laws with large minimum models.
4. Attack one of the 96 finite-trivial laws with unknown infinite-model status.
5. Attack one of the 24 laws with unknown nontrivial finite-model status.
6. Contribute a new lemma, obstruction, model, or full resolution for
   `E677 |=_fin E255`.

At this level, `unsolved` is a legitimate outcome. Progress must be represented
as verified partial results, excluded model families, proved structural lemmas,
or reproducible search improvements.

## 7. Curriculum Data Construction

### 7.1 Problem pools

Maintain separate pools:

**Pool A: routine public problems**

- cheap routing and regression;
- known proof/model artifacts;
- not used as evidence of discovery.

**Pool B: artificial frontiers**

- the full solver succeeds;
- a named completed capability is withheld;
- generic primitives can in principle reconstruct the solution;
- used for recovery training.

**Pool C: structural holdouts**

- unseen members of known families;
- alpha-renamed, dualized, rebracketed, or order-expanded variants;
- used for transfer and anti-memorization tests.

**Pool D: closed research cases**

- historically difficult but now solved ETP cases;
- full artifacts withheld from System 2;
- used to test whether the system independently rediscovers known mathematics.

**Pool E: open or partially open cases**

- E677 finite implication;
- order-5 Austin classification unknowns;
- selected higher-order unresolved candidates;
- used only after earlier gates are met.

### 7.2 Leakage controls

For curriculum claims:

- remove public problem IDs from prompts;
- canonicalize or randomly rename variables;
- hold out complete structural families, not random rows alone;
- test dual equations separately;
- do not retrieve the target's known proof or model;
- distinguish a rediscovered known result from a new result by checking the ETP
  graph, blueprint, repository, and local full solver;
- record every source artifact available to the controller.

### 7.3 Teacher use of the full solver

The full mechanical system may be used offline to:

- identify examples at the right difficulty;
- generate successful proof traces;
- locate the exact missing capability;
- produce negative examples and failed partial plans;
- verify curriculum answers;
- calibrate budgets.

It should not silently leak the winning route into the held-out System 2 prompt.

## 8. Learning and Distillation Loop

Every curriculum cycle should follow:

1. **Select capability:** choose one target skill and capability mask.
2. **Generate episodes:** include successes, near misses, and instructive
   failures.
3. **Canonicalize:** remove problem-specific names and incidental syntax.
4. **Extract lesson:** produce a proposed reusable strategy or decision rule.
5. **Mechanically validate:** ensure examples and claimed artifacts are sound.
6. **Freeze the protocol:** hash prompts/configuration and seal development
   targets before evaluating transfer.
7. **Test transfer:** evaluate repeated trials on held-out families and
   transformations; a target consulted during repair becomes development data.
8. **Distill:** add to retrieval, compact strategy memory, a learned policy, or
   a new System 1 tool.
9. **Reintegrate:** restore the withheld capability and measure combined value.
10. **Ratchet:** move to a harder target instead of continuing to rehearse a
   mastered one.

Distillation artifacts should be typed:

```text
route_policy
parameter_policy
lemma_schema
proof_plan_schema
model_family
invariant
rewrite_system
compiled_tool
negative_obstruction
```

## 9. Evaluation and Attribution

Use three scoreboards rather than one.

### 9.1 Capability scoreboard

Measure:

- recovery rate under declared dropout;
- transfer to held-out families;
- composition of separately learned skills;
- representation-change success;
- verified artifact creation;
- cost and judge-call efficiency;
- adaptation to newly described or missing tools.

### 9.2 Full-system scoreboard

Measure:

- accepted count with all mechanics restored;
- unique LLM-enabled wins against the same full baseline;
- accepted count as a function of total LLM plus mechanical cost;
- regressions and timeouts;
- Solo and Marathon behavior;
- official-container reproducibility.

### 9.3 Mathematical-discovery scoreboard

Measure:

- new verified lemmas;
- new countermodels or model families;
- new impossibility/obstruction results;
- new complete or partial rewrite systems;
- reduction of an open classification set;
- independent reproduction by a clean verifier or external tool.

### 9.4 Attribution vocabulary

Replace the current route-based `llm_load_bearing` label with evidence-based
categories:

```text
native_full_baseline
curriculum_recovery
llm_selected_existing_tool
llm_parameterized_existing_tool
llm_proposed_known_helper
llm_proposed_novel_verified_helper
llm_synthesized_verified_workflow
llm_created_reusable_artifact
integrated_unique_win
candidate_mathematical_discovery
externally_confirmed_discovery
```

An `integrated_unique_win` requires a paired run in which the same full
mechanical capabilities and budget fail without the System 2 contribution.

## 10. Workstreams Mapped to the Existing Repository

### Workstream A: Semantics and correctness

Build first:

- finite/general status records;
- known Austin implication detection;
- a competition certificate-policy switch;
- corrected `hard2_0027` documentation;
- explicit infinite-model action and feedback classes.

Relevant current files:

- `official-stage2/judge/verify.py` for the executable goal;
- `official-stage2/rules/evaluation.md` for intended policy;
- `baby_solver.py` false-search scheduler;
- `docs/collaborative_solver_roadmap.md` and `docs/flywheel_platform_evidence.md`
  for frontier diagnoses and evidence tracking.

### Workstream B: Curriculum harness v2

Generalize `scripts/midpoint_curriculum_probe.py` into a capability-dropout
runner rather than replacing it.

Add:

- capability masks;
- arbitrary tool withholding;
- paired full/handicapped execution;
- family-level train/validation/test splits;
- randomized variable renaming and dualization;
- true, finite-false, and infinite-false curricula;
- structured episode output;
- transfer reports.

The existing midpoint curriculum remains the first Level-3 dataset.

### Workstream C: Protocol v1 and blackboard

Evolve `docs/mechanical_llm_protocol_v0.md` and
`docs/system1_system2_protocol.md` into a typed state/action system supporting:

- proof-plan DAGs;
- semantic classification;
- representation proposals;
- model families and invariants;
- capability manifests;
- explicit cost accounting;
- reusable artifact candidates.

Prototype this in `scripts/llm_lean_sidecar.py` before packing it into
`baby_solver.py`.

### Workstream D: Experience store and distiller

Extend the current `.artifacts` practice from many unrelated JSON files into an
indexed episode ledger with:

- schema version;
- problem signature;
- capability mask;
- action/observation trace;
- verifier outcome;
- cost;
- counterfactual;
- distillation status;
- research novelty status.

Raw artifacts remain immutable evidence. A separate index and compact distilled
library should point to them.

### Workstream E: General mechanical substrates

Strengthen mechanics that increase System 2 leverage:

- proof-producing equality saturation;
- assumption-aware completion/superposition;
- compact proof-plan obligation checking;
- finite CSP with goal falsification, propagation, and symmetry breaking;
- symbolic and infinite model templates;
- artifact minimization.

Do not prioritize more one-off renderers unless they serve as curriculum
teachers or compile a System 2 discovery.

### Workstream F: Research frontier suite

Create reproducible case packs for:

- E3523 rewrite-system rediscovery;
- known Austin implications, including 1167 -> 1763;
- known order-5 Austin laws;
- selected large-minimum-model order-5 laws;
- E5093 infinite-model status;
- E677 finite implication;
- the higher-order unresolved candidates documented by ETP.

Each pack should separate public background, hidden reference artifacts, legal
controller inputs, mechanical validators, and novelty checks.

### Workstream G: Competition integration

Keep `baby_solver.py` and the packed submission working while research proceeds.

Requirements:

- official Docker reproduction;
- unavailable research tools excluded from production manifests;
- Solo and eventual Marathon support;
- a full-strength submission with no curriculum dropout;
- a clear mapping from research modules to the packed build;
- no competition-score claim based only on handicapped runs.

## 11. Phased Implementation Plan

### Phase 0: Correct the map

Deliverables:

1. Freeze and hash the current full-strength baseline.
2. Add a semantic registry for known general/finite outcomes.
3. Correct all `hard2_0027` frontier descriptions.
4. Define certificate-policy modes.
5. Replace route-based load-bearing attribution in new reports.
6. Record a deployment-faithful baseline under the official environment.

Exit criterion: the project no longer spends finite-search budget on a known
finite implication and every result states which semantics it concerns.

### Phase 1: Make dropout experimental rather than architectural

Deliverables:

1. Capability manifest for current `TOOL_REGISTRY` entries and specialized
   deterministic routes.
2. A curriculum runner that can withhold capabilities without editing solver
   code.
3. Paired full/handicapped result format.
4. Reproduction of the existing midpoint curriculum through the new runner.
5. Family-level held-out tests and syntax transformations.

Exit criterion: existing Level-3 recovery results are reproducible with an
explicit capability mask and no full-baseline regression.

### Phase 2: Move from route choice to proof planning

Deliverables:

1. Blackboard schema and protocol v1 prototype, including immutable verified
   nodes and explicitly refuted nodes.
2. Lemma DAG actions and node-specific feedback, including concrete small
   countermodels where available.
3. Compact plan repair loop that extends proved partial plans instead of
   regenerating the entire answer.
4. At least one cross-family composition case.
5. A verified non-hardcoded helper that transfers to a second case.

Exit criterion: System 2 contributes a reusable mathematical abstraction, not
only the name or parameters of an existing solver.

### Phase 3: Close the learning loop

Deliverables:

1. Indexed episode ledger.
2. Automated canonicalization and lesson extraction.
3. Retrieval versus compact-distillation comparison.
4. Ratcheting rules for mastered capabilities.
5. Reintegration reports measuring combined-system value.

Exit criterion: a verified artifact learned in one curriculum cycle improves a
later held-out problem after the full mechanical system is restored.

### Phase 4: Representation-changing System 2

Deliverables:

1. Finite/general/infinite route classifier.
2. Model-family and invariant action schemas.
3. Known infinite-model reconstruction suite.
4. E3523 rewrite-system rediscovery experiment.
5. At least one compiled workflow or representation artifact.

Exit criterion: System 2 creates a verified artifact that changes which
mechanical search is possible or efficient.

### Phase 5: Open-frontier research

Deliverables are result-dependent rather than time-dependent:

- verified partial lemmas;
- excluded model families;
- new finite or infinite models;
- reduced candidate sets;
- improved proof/model search procedures;
- formalized resolutions when found.

Begin with closed historical cases, then graduate to order-5 unknowns and E677.

## 12. Immediate Next Candidate Actions

Do not begin broad E677 or order-5 search yet. Vertical Slices 3 through 5
completed the first versions of state, live planning, verified branching,
distillation, and deployment. While concrete System-2 capability gaps remain,
development takes priority over broad comparative measurement:

1. **Implemented v1 — freeze an evaluation contract.** Record model/provider,
   decoding settings, prompt hash, capability manifest hash, code revision,
   budgets, and random seeds where supported. Separate `development`,
   `sealed_test`, and `postmortem` labels in every artifact.
2. **Implemented v1 — make partial progress first-class state.** Move the
   monotone-progress rule out of prompt prose and into a blackboard/lemma-DAG
   object. A proved lemma is immutable trusted state; a countermodel-refuted
   lemma is blocked up to alpha equivalence; only unresolved nodes are
   regenerated.
3. **Implemented v1 — teach structural abstraction from verified experience.**
   Typed proof-plan lessons are now retrieved by equation structure, capability
   state, and verified partial-plan overlap rather than problem ID or raw
   transcript. An alpha-renamed/equality-reversed right-square continuation is
   solved only with retrieval enabled, selecting one missing node, while an
   unrelated negative retrieves nothing. Magma-dual matching transports dualized
   helpers. Next expand beyond this one family and require a helper schema absent
   verbatim from retrieval. See `docs/structural_retrieval_v1.md`.
4. **Implemented v1 — expand the System-2 action language.** A `proof_plan`
   action now creates an approach-family registry with executable dependencies,
   diverse ready alternatives, mechanical lifecycle evidence, automatic
   continuation, blocking, and novelty-gated reopening. A one-turn right-square
   plan proved its square route, mechanically refuted a projection alternative,
   automatically ran the dependent node, and passed Lean. Next make
   attain/consume/audit legs explicit and add root-level AND/OR value
   propagation. See `docs/obligation_graph_v1.md`.
5. **Next — build the development curriculum.** Add solve-from-scratch and verified
   partial-plan continuation tasks across at least four structural families,
   including alpha-renamings, duals, syntactic disguises, and two-family
   compositions. Promote difficulty as soon as a capability is reliable.
6. **Distill after demonstrated reuse.** Store the verified protocol lesson
   (`retain proved nodes; reject refuted alpha-equivalents`) as a typed strategy
   artifact and compile a mathematical helper only after it improves a later
   task. Do not compile a family-specific chain merely because it appeared in a
   few-shot.
7. **Structure the infinite-model lane.** Replace whole-file Lean submission as
   the main research action with a parameterized model-family schema: carrier,
   operation, proof obligations for H, and a concrete witness violating G.
   Reconstruct several closed historical Austin countermodels before attempting
   an unresolved case.
8. **Audit deployment separately.** Minimize the E3994 -> E3588 proof against
   the competition declaration policy or record precisely why it cannot be made
   submission-compatible. Keep research soundness and competition deployability
   as separate scorecard fields.
9. **Defer broad A/B measurement until it changes a decision.** Once the above
   capability work no longer has an obvious next step, freeze a multi-family
   suite and compare full mechanics, handicapped mechanics, live System 2, and
   external baselines under equal total budgets.

If only one item is selected, choose item 5 while using each curriculum case to
drive the next graph increment. Structural transfer and dependency-aware
portfolio execution now each work for one controlled family; the next need is
pressure from dual, disguised, multi-family, and absent-verbatim tasks rather
than another context-free platform module.

## 13. Risks and Stop Rules

### Risk: prompt memorization masquerades as learning

Controls:

- family holdouts;
- problem-ID removal;
- alpha renaming and dualization;
- novel tool descriptions;
- structural transfer tests.

### Risk: the LLM learns to perform low-level bookkeeping badly

Control: preserve exact primitives and withhold only completed solutions.

### Risk: a frozen model never actually improves

Control: require every cycle to end in explicit distillation, retrieval,
fine-tuning data, or a compiled tool. Repeated evaluation alone is not progress.

### Risk: curriculum success does not help the full system

Control: every mastered capability must be reintegrated and evaluated for
transfer, efficiency, or unique coverage.

### Risk: verifier calls become blind search

Controls:

- cap judge attempts;
- preflight mechanically;
- require compact proof traces;
- penalize candidates predicted to cause Lean explosion.

### Risk: open-problem work produces inflated claims

Controls:

- separate rediscovery from novelty;
- check ETP data, blueprint, repository, and current literature;
- require clean reproduction;
- label unverified results as conjectures;
- publish partial results with exact assumptions and search bounds.

### Risk: competition and research environments silently diverge

Control: tag every tool and result with its environment and deployability. A
research-only tool may be valuable without being described as submission-ready.

## 14. Definition of Success

The project succeeds scientifically before it solves an open problem if it can
show a credible progression:

1. System 2 reconstructs deliberately withheld capabilities.
2. The reconstruction transfers beyond the examples that taught it.
3. Separate capabilities compose on unseen cases.
4. Verified episodes become reusable abstractions or tools.
5. The full system becomes stronger after those tools are restored.
6. System 2 proposes representation-level artifacts that were absent from the
   original portfolio.
7. The combined system produces new, independently verified mathematics.

Competition improvements are welcome evidence at every stage, but the central
measure is whether the system's capacity to create and organize exact
mathematical reasoning is expanding.

## 15. Primary Sources

- [SAIR Stage 2 overview](https://competition.sair.foundation/competitions/mathematics-distillation-challenge-equational-theories-stage2/overview)
- [SAIR Stage 2 evaluation setup](https://competition.sair.foundation/competitions/mathematics-distillation-challenge-equational-theories-stage2/evaluation-setup)
- [Official Stage 2 repository](https://github.com/SAIRcompetition/equational-theories-lean-stage2)
- [Current false-goal implementation](https://github.com/SAIRcompetition/equational-theories-lean-stage2/blob/main/judge/verify.py#L282)
- [Equational Theories Project paper](https://teorth.github.io/equational_theories/paper.pdf)
- [ETP dashboard and blueprint](https://teorth.github.io/equational_theories/)
- [Equation 677 chapter](https://teorth.github.io/equational_theories/blueprint/677-chapter.html)
- [Order-5 Austin-law classification](https://teorth.github.io/equational_theories/blueprint/order-5-austin-laws.html)
- [Austin finite-only implications](https://raw.githubusercontent.com/teorth/equational_theories/main/data/Austin_implications.txt)
- [Distilling Many-Shot In-Context Learning into a Cheat Sheet](https://arxiv.org/abs/2509.20820)
