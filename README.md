# SAIR-Maths-Distillation-Stage-2

## Background: the Mathematics Distillation Challenge

[SAIR](https://sair.foundation)'s Mathematics Distillation Challenge asks whether the knowledge
inside a large machine-generated mathematical corpus — implications between equational theories —
can be distilled into compact artifacts that transfer. Stage 1 asked for a "cheatsheet": a short
document that teaches an LLM to predict whether one equational theory implies another. Our Stage-1
submission [placed 3rd](https://competition.sair.foundation/leaderboard/mathematics-distillation-challenge-equational-theories-stage1).

One Stage-1 finding shaped how we think about this problem. Our highest-scoring cheatsheet drafts
were not, strictly speaking, mathematically correct — they contained rules that predicted well but
were logically unsound. More interestingly, every attempt to keep a draft close to the top scorer
while nudging it slightly toward rigor *lowered* its score, consistently. We submitted the
mathematically valid version anyway, and kept the observation: the most effective educational
material for a model on this task was not the most rigorous one — as is often true, in our
experience, of educational material for humans.

Stage 2 raises the bar from prediction to verification: instead of a cheatsheet that guesses
implications, the goal is deterministically checkable artifacts — Lean-certified proofs and
explicit counterexamples. This repository is our working solver and research harness for that.

## This repository

This repository contains a solver and research harness for the
[SAIR Stage 2 equational-theories competition](https://github.com/SAIRcompetition/equational-theories-lean-stage2).
Each problem asks whether one universally quantified equation over a magma
implies another. A valid answer is either a Lean proof of the implication or a
Lean-checkable countermodel.

The project explores a collaborative architecture: an LLM may propose tool
calls, intermediate lemmas, proof plans, or countermodel-search routes, but the
mechanical side must prove or refute those proposals. Lean is the final source
of truth.

This is a public, history-free snapshot of an active research repository rather
than a polished Python library. Raw experiment transcripts, generated runner
artifacts, and the upstream Lean checkout are intentionally omitted from this
repo; the code regenerates those locally when the relevant scripts are run. A
small curated [`evidence/`](evidence/) directory is committed so the main
LLM/mechanical interaction claims can be inspected without the private
workbench.

The most useful orientation documents are:

- [`docs/project_overview.md`](docs/project_overview.md): motivation, architecture, and evidence;
- [`docs/research_system_architecture.md`](docs/research_system_architecture.md): modular research harness and competition compilation;
- [`docs/teacher_student_symbolic_model_plan.md`](docs/teacher_student_symbolic_model_plan.md):
  active roadmap for verified teacher-student distillation and symbolic
  countermodels.

## Repository map

- `baby_solver.py`: maintained packed solver source and mechanical backend.
- `research_system/`: modular curriculum, planning, obligation, verification,
  experience, and distillation components.
- `scripts/run_research_episode.py`: run scripted or live-LLM research episodes.
- `scripts/teacher_student_search.py`: run resumable mechanically ranked
  teacher search and ordinary-student attribution.
- `baby_solver.py` also exposes native `skew_product:QxF` false-search routes;
  `scripts/skew_model_probe.py` and `scripts/bundle_model_probe.py` explore
  equal- and unequal-fiber extensions and verify their expanded tables.
- `scripts/bundle_feedback_probe.py`: test live repair across a failed
  equal-fiber family and progressively larger non-uniform bundles.
- `scripts/structured_infinite_model_probe.py`: assemble and judge a typed
  infinite countermodel plan.
- `scripts/research_system_contracts.py`: fast contract and regression checks.
- `scripts/compile_submission.py`: compile the current system into a single
  competition-compatible `solver.py`.
- `scripts/compiled_submission_smoke.py`: exercise a compiled solver through
  the official proxy and Lean judge.
- `configs/`: checked-in example LLM configuration files that read credentials
  from environment variables.
- `docs/`: design notes, protocols, roadmaps, and evidence summaries.
- `evidence/`: curated public audit summaries and end-to-end case studies.

The local `.artifacts/` and `sidecar_runs/` directories contain generated
reports, builds, model transcripts, and proof artifacts. They are intentionally
not committed in this public snapshot. Some historical documents refer to files
there; the committed `evidence/` files are small sanitized derivatives.

## Environment setup

### Required upstream checkout

Python 3.11 is recommended. Clone the official Stage 2 repository beside the
project files at the expected path, then follow its setup instructions to
install the pinned Lean toolchain and Mathlib environment:

```bash
git clone https://github.com/SAIRcompetition/equational-theories-lean-stage2.git official-stage2
cd official-stage2
bash scripts/setup.sh
cd ..
source official-stage2/.env.judge
```

The `official-stage2/` checkout is ignored by this repository because it is an
independent upstream project. Its setup script installs the pinned Lean
toolchain, fetches Mathlib through Lake, builds the judge modules, and writes
`official-stage2/.env.judge`. Source that file in each new shell before running
the local verifier if `lean` and `lake` are not already on `PATH`.

No separate external solver checkout is required. The old embedded compatibility
solver has been retired; the retained proof and countermodel mechanisms are
source-independent implementations in `baby_solver.py`. The
`teorth/equational_theories` repository is also not a required checkout; the
semantic registry snapshot is committed under `data/`, and
`scripts/update_semantic_registry.py` accesses its upstream source over HTTPS
only when explicitly refreshing that snapshot.

### Python packages

Create a virtual environment if desired, then install the required
OpenAI-compatible client used by the official pipeline and the LLM/Lean sidecar:

```bash
python3 -m venv .venv
source .venv/bin/activate
python3 -m pip install -r requirements.txt
```

OR-Tools is optional. Install it to enable the local `cp_sat:n=k`
countermodel-search route; without it, that route reports `unavailable` and the
other search routes continue normally:

```bash
python3 -m pip install -r requirements-optional.txt
```

### LLM credentials

Keep provider keys in environment variables, never in committed JSON. Every
LLM configuration should set both `llm.base_url` and `llm.api_key_env` so that
the intended key is selected even when several provider keys are present. For
example, the committed Cerebras configuration expects:

```bash
export CEREBRAS_API_KEY="<your key>"
python3 scripts/run_research_episode.py \
  --planner llm \
  --llm-config configs/cerebras_gpt_oss_120b.example.json
```

For another OpenAI-compatible provider, export the variable named by that
configuration, such as `OPENAI_API_KEY` or `OPENROUTER_API_KEY`, and set the
matching `"api_key_env"` field. `OPENAI_BASE_URL` is supported as an override,
but an explicit `base_url` in the configuration is less ambiguous.

Scripted reference episodes and most mechanical checks do not require an LLM
key.

## Quick checks

Run the modular contract suite:

```bash
python3 scripts/research_system_contracts.py
python3 scripts/native_import_audit.py
```

Run the three scripted reference curriculum lanes:

```bash
python3 scripts/run_research_episode.py
```

Build and smoke-test a one-file competition submission:

```bash
python3 scripts/compile_submission.py
python3 scripts/compiled_submission_smoke.py
```

Generated outputs are written beneath `.artifacts/`.

The generated competition submission is written to
`.artifacts/compiled_submission/submission/solver.py`. It is not checked in, so
there is one maintained solver source in the public tree.

## Credits

This solver builds on the official SAIR Stage 2 library and pipeline and the
Equational Theories Project corpus. It also reimplements or adapts ideas from
public Stage-2 solver entries including marathon DSL-solver, WILL, EULER,
opnorm, the SAIR baseline, and Contribution Solver .7 / Foundation, plus
classical automated-reasoning work on completion, paramodulation/superposition,
finite-model finding, and LNH symmetry breaking. We intentionally err on the
side of crediting influences; see [`CREDITS.md`](CREDITS.md).

## Working conventions

- Treat LLM output, proposed lemmas, and candidate countermodels as untrusted.
- Count a result only after the official Lean verifier accepts it.
- Preserve attribution between native mechanical, imported mechanical, and
  load-bearing LLM contributions.
- Prefer small focused probes over broad expensive sweeps while developing.
- Never commit API keys or provider configuration containing credential values.

For the current architecture and research direction, start with
[`docs/project_overview.md`](docs/project_overview.md).

This project is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE).
