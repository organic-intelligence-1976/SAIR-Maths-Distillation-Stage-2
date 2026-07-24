# Credits

This project is an independent public implementation for the
[SAIR Mathematics Distillation Challenge, Equational Theories Stage 2][sair-stage2].
It builds on public competition infrastructure, public problem data, classical
automated-reasoning literature, and ideas observed in public Stage-2 solver
entries.

Attribution names and solver IDs below follow the [SAIR Contributor Network][sair-contributors]
snapshots and local attribution notes reviewed during development. The live
Contributor Network is partially client-rendered, so not every display name was
equally easy to re-check from a static page. We intentionally err on the side of
crediting influences. If any name, ID, or influence is incomplete or misnamed,
please open an issue or pull request and we will correct it.

Unless otherwise noted, credits below describe ideas, algorithms, examples, or
public solver patterns that were reimplemented or adapted. This repository is
intended as a source-independent solver and research harness.

## Competition Infrastructure

- **[SAIR Foundation Stage 2 official library and pipeline][sair-stage2]**: the Lean judge,
  proxy protocol, input/output shape, and reference setup used by Stage 2. All
  Lean proof and countermodel certificates produced here target that official
  interface.
- **[Equational Theories Project][equational-theories]**: the magma-law corpus, equation numbering,
  implication graph, and semantic-registry lineage behind the Stage-2 task.
  This repo includes a small committed semantic snapshot under `data/semantics/`
  for local research workflows.
- **[Lean 4][lean] and [Mathlib][mathlib]**: the proof assistant and library used by the official
  verifier. In particular, Lean tactics such as `grind` are load-bearing in many
  true-side certificates emitted by this solver.

## Public Stage-2 Solver Influences

- **marathon DSL-solver** (`EQT02-M00006`, display name recorded as
  omegaestable): a major influence for tuple-style term representation,
  parsing/subterm/instantiation helpers, bounded rewrite-chain routes, small
  witness banks, structured countermodel families, affine and quadratic finite
  model sweeps, transpose/dual fallbacks, and the discipline of verifying
  candidates locally before sending them to the judge.
- **WILL v1** (`EQT02-M00005`, Christopher Brock / Riemann Labs): influenced
  the term-representation lineage, the `HAVE+GRIND` strategy of hypothesis
  instantiation followed by Lean closure, and common Lean-body cleanup patterns.
- **EULER v4/v5 and successor entries** (`EQT02-S00018`, `EQT02-S00020`,
  Riemann Labs / Christopher Brock): influenced the `HAVE+GRIND` taxonomy,
  helper-lemma generation, and "Tao lemma synthesis" style of deriving
  universal auxiliary facts as stepping stones.
- **Contribution Solver .7 / Foundation** (`EQT02-S00007`, display names
  recorded as Dufius / BringOn): reinforced the verify-locally-before-judge
  workflow for finite models and generated certificate bodies.

## SAIR Official Samples and Demos

- **SAIR baseline** (`EQT02-S00001`, SAIR Official): the basic judge-protocol
  pattern and reference one-file solver shape.
- **opnorm** (`EQT02-S00002`, SAIR Official): constancy-engine and library-lemma
  patterns, including auxiliary facts such as constant operation, projection, and
  row-constant laws handed to Lean for closure; also the practical operator
  normalization issue between textual `*` and `◇`.
- **twophase demo** (`EQT02-S00003`, SAIR Official): additional reference
  examples for the proxy/wrapper protocol and phased solver structure.

## Classical Automated-Reasoning Literature

- **Resolution and paramodulation**: J. A. Robinson's resolution method and the
  Robinson-Wos paramodulation lineage underlie equality reasoning and
  proof-carrying rewrite search.
- **Superposition**: Bachmair-Ganzinger style superposition informs the
  proof-carrying saturation helpers used on the true side.
- **Knuth-Bendix completion**: completion-style orientation and rewriting are
  part of the conceptual background for several rewrite-chain routes.
- **Unfailing completion**: Bachmair, Dershowitz, and Plaisted's "Completion
  Without Failure" and later compact provers such as Twee influenced the
  grounding and derived-lemma closers.
- **Finite-model finding**: Mace4-style model search, Paradox-style constraint
  encodings, and LNH/SEM symmetry-breaking ideas inform the false-side search
  modules.

## Libraries

- **Python 3.11** standard library: the solver and research harness are plain
  Python.
- **[OpenAI Python client][openai-python]**: used for optional OpenAI-compatible LLM calls in
  research episodes.
- **[Google OR-Tools][or-tools]**: optional dependency for the CP-SAT countermodel-search
  route.

## Influence Map

| Public-repo mechanism | Main credits |
| --- | --- |
| Tuple term representation, parsing, and subterm helpers | marathon DSL-solver; WILL v1 |
| Equality-graph search and `HAVE+GRIND` instantiation | WILL v1; EULER; marathon DSL-solver rewrite-chain lineage |
| Calc-chain and target-path search | marathon DSL-solver; classical rewrite search |
| Helper-lemma families for constancy, projection, and row-constant behavior | opnorm; EULER "Tao lemma synthesis" |
| Lean-body cleanup and wrapper normalization | SAIR baseline; WILL v1; opnorm; official demos |
| Witness tables and structured/affine/quadratic countermodel families | marathon DSL-solver |
| Verify-locally-before-judge workflow | marathon DSL-solver; Contribution Solver .7 / Foundation |
| Proof-carrying superposition helpers | Robinson-Wos paramodulation; Bachmair-Ganzinger superposition |
| Grounding and derived-lemma closers | Bachmair-Dershowitz-Plaisted; Twee |
| Goal-directed finite-model search and symmetry pruning | Mace4/Paradox lineage; LNH/SEM |
| `finOpTable`, `decideFin!`, and proxy certificate scaffolding | SAIR official Stage-2 library |
| Problem corpus, equation numbering, and semantic snapshot | Equational Theories Project |
| Lean `grind`-based final certificates | Lean 4 / Mathlib |

## Project-Specific Work

The collaboration protocol, tool registry, structured mechanical feedback,
curriculum harness, LLM-midpoint verification loop, attribution accounting, and
some goal-directed countermodel heuristics were developed inside this project.
They are listed here to separate local engineering work from external
influences, not to make a broad novelty claim.

[sair-stage2]: https://github.com/SAIRcompetition/equational-theories-lean-stage2
[equational-theories]: https://github.com/teorth/equational_theories
[sair-contributors]: https://competition.sair.foundation/contributor-network?competition=mathematics-distillation-challenge-equational-theories-stage2
[lean]: https://lean-lang.org/
[mathlib]: https://github.com/leanprover-community/mathlib4
[openai-python]: https://github.com/openai/openai-python
[or-tools]: https://developers.google.com/optimization
