# Modular Research System and Competition Compilation

Status: walking skeleton operational, 2026-07-26

The project now has two deliberately different products:

1. `research_system/`: a modular environment for curriculum experiments,
   verified repair, experience, distillation, and evaluation;
2. a generated single-file `solver.py`: the competition deployment snapshot.

The packed `baby_solver.py` remains the first mechanical backend and the first
compiler source unit. It is wrapped rather than immediately dismantled. This
lets the modular architecture run real experiments while individual engines are
migrated only after their interfaces are stable.

## Executable flow

```text
CurriculumCase
  -> SemanticService
  -> Planner
  -> LemmaBlackboard
  -> MechanicalExecutor (baby_solver adapter)
  -> OfficialLeanVerifier
  -> ExperienceStore
  -> VerifiedDistiller
  -> IntegrationCatalog
  -> SubmissionCompiler
```

All mathematical proposals from planners remain untrusted. A blackboard node is
trusted only after mechanical proof, and an episode is accepted only after the
official Lean verifier accepts the final artifact.

## Components and current minimal implementations

| Component | File | Working v1 behavior |
|---|---|---|
| Protocol | `research_system/protocol.py` | Versioned problem, execution, verification, episode, and strategy-artifact records |
| Semantics | `research_system/semantics.py` | Source-stamped Austin lookup, data-driven status overrides, competition-row fallback |
| Capabilities | `research_system/capabilities.py` | Manifests, masks, gates, and intervention eligibility audit |
| Blackboard | `research_system/blackboard.py` | Immutable proved nodes and alpha-canonical small-model refutations |
| Obligation graph | `research_system/obligations.py` | Approach families, executable dependencies, diverse alternatives, blocking, and novelty-gated reopening |
| Planner | `research_system/planner.py` | Deterministic scripted planner, callable adapter, live OpenAI-compatible planner, and bounded feedback-correction wrapper |
| Teacher search | `research_system/teacher.py` | Resumable mechanically ranked beams, trajectory minimization, and counterfactual ordinary-student replay |
| Budget broker | `research_system/budget.py` | Renewable geometric worker leases, tunable policy genotypes, and reproducible mutation |
| Executor | `research_system/executor.py` | True lemma/tool actions, finite tables/search, direct proofs, structured infinite plans, and legacy artifacts through `baby_solver.py` |
| Finite-model contract | `research_system/finite_models.py` | Equal-fiber skew products, non-uniform quotient bundles, sparse affine-map patches, CEGIS verification, and congruence decomposition |
| Infinite-model contract | `research_system/infinite_models.py` | Typed model parts, safe syntax normalization, field patches, and deterministic Lean assembly |
| Verifier | `research_system/verifier.py` | Official Lean checks under competition or research declaration policy |
| Curriculum | `research_system/curriculum.py` | True-dropout, finite-false, and infinite-false reference episodes |
| Orchestrator | `research_system/orchestrator.py` | Multi-round propose/check/retain/refute/verify loop |
| Structure | `research_system/structure.py` | Alpha/orientation invariant and magma-dual problem/lemma fingerprints |
| Experience | `research_system/experience.py` | Append-only ledger plus attributed structural, capability, and partial-plan retrieval |
| Distillation | `research_system/distillation.py` | Accepted episode to typed verified proof-plan lesson, finite model, or infinite-model artifact |
| Evaluation | `research_system/evaluation.py` | Paired full/curriculum/negative runs where applicable |
| Integration | `research_system/integration.py` | Promotion gate for verified competition candidates |
| Compiler | `research_system/compiler.py` | Reproducible one-file build, AST/PROMPT/layout/size checks, and manifest |

These are thin implementations, not empty interfaces. Their extension points
are stable enough for separate improvement.

## Reference episode results

Run:

```bash
python3 scripts/run_research_episode.py
```

The first complete run produced:

| Lane | Result | Distilled artifact |
|---|---|---|
| Right-square true proof with focused tool withheld | generic two-step blackboard recovery accepted; full baseline accepted; negative control failed | `proof_plan_schema` |
| Finite false implication (`hard1_0006`) | size-2 table accepted | `model_instance` |
| Austin E3994 -> E3588 unrestricted false implication | Type-level model accepted under research policy | `infinite_model_artifact` |

The run recorded five episodes (curriculum plus controls), four accepted
episodes, and three verified artifact types. Evidence is in
`.artifacts/walking_skeleton_reference_v1.json` and
`.artifacts/walking_skeleton_experience_v1/`.

## Live stateful System 2

The modular CLI now has a real LLM path rather than only scripted reference
actions:

```bash
python3 scripts/run_research_episode.py \
  --planner llm \
  --case reference_true_right_square \
  --retrieval-limit 0 \
  --max-rounds 6
```

Each turn receives a capability-aware action menu, the trusted/refuted lemma
blackboard, and compact mechanical diagnostics rather than a raw prover dump.
Provider traces record prompt hashes and usage without trusting or hiding the
returned mathematical action. Indexed feedback variables such as `v0` and
`v1` are accepted by the hint parser.

Verified partial progress is now resumable across sessions:

```bash
python3 scripts/run_research_episode.py \
  --planner llm \
  --case reference_true_right_square \
  --resume-report .artifacts/research_system_live_system2_v2.json \
  --max-rounds 6
```

Only nodes marked `mechanically_proved` or `small_model_refuted` are restored.
The last compact observations are also restored. Candidate batches are
supported through one `lemma_chain` action: refuted repeats are filtered
individually, every proved candidate is retained, and an unproved candidate
does not erase the rest of the plan.

The first development runs are deliberately not coverage claims:

- v2, with no retrieval, ended unsolved but accumulated two proved and two
  refuted universal lemmas;
- v4 resumed from one verified helper and proved one additional generalized
  bridge;
- v5 exercised branching, proposed three candidates in one turn, retained one
  newly proved candidate, and recorded two decisive refutations before ending
  unsolved.

Artifacts are
`.artifacts/research_system_live_system2_v2.json`,
`.artifacts/research_system_live_system2_v4_partial_continuation.json`, and
`.artifacts/research_system_live_system2_v5_branching_resume.json`. These runs
show that the live loop now preserves and expands verified mathematical state.
They also expose the next capability gap: System 2 follows local closest-pair
diagnostics too literally and needs a curriculum/retrieval layer that teaches
reusable abstraction from those diagnostics.

## Teacher search and structured models

The teacher harness explores several independent actions per state and ranks
them only by mechanically observed progress:

```bash
python3 scripts/teacher_student_search.py \
  --id hard2_0093 \
  --focus finite_symbolic \
  --beam-width 2 \
  --proposals-per-branch 3
```

Reports contain a resumable beam checkpoint. Exact bounded propagation probes
also prevent the LLM from proposing carriers already eliminated by the
mechanical side.

Finite symbolic search now has two compositional constructors. A skew product
uses equal fibers; a bundle permits unequal fiber sizes and sparse exceptions
to local affine maps while preserving an exact quotient. Mechanical
`family_infeasible` states retain that specific status, emit primary and
secondary next-action schemas, and receive one bounded correction reprompt if
the live planner repeats the rejected configuration. The `hard2_0125` case
demonstrates the ladder `2x2 -> [3,2] -> [4,2]`, ending in an official
judge-accepted six-element countermodel. See
[`../evidence/case_study_recursive_bundle_countermodel.md`](../evidence/case_study_recursive_bundle_countermodel.md).

Structured infinite countermodels use a smaller repair surface than whole-file
Lean generation:

```bash
python3 scripts/structured_infinite_model_probe.py
python3 scripts/structured_infinite_repair_probe.py --student-replay
```

The first command assembles and verifies a known five-part `ℕ` model. The
second injects a rejected proof component, lets a live planner repair it from
Lean diagnostics, minimizes the accepted trajectory, and can run no-lesson and
with-lesson student controls. Public results and caveats are in
[`../evidence/case_study_structured_infinite_repair.md`](../evidence/case_study_structured_infinite_repair.md).

## Competition compilation

Run:

```bash
python3 scripts/compile_submission.py
```

The v1 compiler treats `baby_solver.py` as one legacy packed source unit. It:

- requires the competition entry definitions and a literal top-level `PROMPT`;
- emits the checked-in `submission/` directory containing exactly one regular
  `solver.py`;
- validates Python syntax and the 500,000-byte limit;
- records input/output hashes, capability IDs, and policy-sensitive capability
  metadata;
- keeps the infinite-model action available only through the audited semantic
  lane that blocks finite-table search first.

The current build remains below the 500,000-byte limit and passes an official
proxy/judge protocol smoke with zero LLM calls and one accepted Lean call.

This v1 compiler does not yet tree-shake definitions from the packed legacy
source. Its manifest records policy-sensitive definitions explicitly. The next
compiler backend should inline individually marked competition-safe units and
remove unreachable experimental code.

## Contract checks

Run:

```bash
python3 scripts/research_system_contracts.py
```

The fast suite checks every component boundary, including semantic lookup,
capability manifests, alpha-canonical blocking, planner exhaustion, reference
lanes, stateful feedback, verified episode resume, candidate filtering,
indexed feedback variables, finite-family repair feedback, teacher beam resume,
structured infinite-model assembly/repair, experience persistence, promotion
filtering, and single-file builds.

## Next improvement frontier

The skeleton is complete enough that the next work can be expressed as module
improvements:

1. promote midpoint attain/consume/audit work into explicit obligation nodes and
   propagate value through AND dependencies and OR alternatives;
2. expand the working structural-retrieval probe from one alpha/orientation
   continuation into dual, disguised, composed-family, and absent-verbatim
   abstraction exercises;
3. exercise context-masked independent portfolio proposal and later
   cross-family synthesis with a live LLM;
4. exercise the same blinded retrieval contract with a live LLM and compare it
   with no retrieval and raw-lesson controls;
5. migrate capability eligibility auditing out of the older midpoint script;
6. replace the compiler's legacy packed source unit with competition-safe
   modular units and reachability-based tree shaking;
7. make infinite models parameterized model-family artifacts rather than only
   whole Lean source files.

Broad comparative evaluation remains necessary later, but it is not the next
development blocker while these concrete System-2 capabilities are absent.
