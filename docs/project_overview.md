# Project Overview

This project explores a collaborative solver architecture for the SAIR Stage 2
mathematics distillation challenge. The central question is how a language model
and a trusted mechanical proof system can cooperate without making the language
model part of the trusted base.

Each problem asks whether one universally quantified magma equation implies
another. A valid output is either a Lean proof of the implication or a
Lean-checkable countermodel. The solver treats all LLM output as an untrusted
proposal: intermediate lemmas, proof routes, and countermodel-search strategies
must still be independently verified by mechanical code and ultimately by Lean.

## Architecture Hypothesis

The project is organized around a simple division of labor:

- The mechanical layer is responsible for soundness. It constructs equality
  graphs, proof-carrying superposition traces, helper lemmas, finite
  countermodels, and Lean certificate bodies.
- The LLM layer is responsible for strategy at the frontier. It proposes
  midpoint lemmas, lemma chains, route choices, and countermodel-search
  continuations when the mechanical layer reports a structured failure.
- The protocol layer translates between them. Mechanical attempts return compact
  states describing what was proved, what failed, what terms are close, and what
  kind of hint would be useful next.

The intended long-term shape is recursive:

```text
prove_or_refute(H, G):
    try trusted mechanical construction
    if it succeeds, return a Lean-checked artifact
    otherwise expose a structured stuck state
    ask an LLM for one or more untrusted strategic moves
    mechanically prove/refute each proposed move
    recurse on smaller proof or countermodel obligations
```

This is useful only if the LLM can actually change outcomes. The repository
therefore tracks load-bearing LLM contributions separately from native
mechanical solves. A language-model call counts as useful only when its proposed
hint, route, or repair is consumed by the mechanical layer and the final Lean
artifact is accepted.

## Mechanical Components

The current solver includes several families of trusted constructors:

- bounded equality-graph search over instantiated hypotheses;
- proof-carrying superposition and paramodulation-style helper proving;
- focused helper families for square absorption, row-constant behavior,
  projection behavior, and related equational patterns;
- generic midpoint and lemma-chain consumers;
- finite countermodel search, including local search, propagation-style search,
  and an optional CP-SAT route when OR-Tools is installed;
- attribution and audit scripts that distinguish native mechanical solves from
  LLM-selected routes and LLM-proposed lemmas.

Some of these mechanisms were inspired by stronger historical mechanical
baselines. In this public snapshot they are integrated as source-independent
tools: the solver does not launch an opaque external solver as a hidden fallback.

## LLM Collaboration Surfaces

The main LLM-facing actions are:

- `tool_call`: select a registered mechanical tool and parameters;
- `lemma_hint`: propose a single midpoint equation;
- `lemma_chain`: propose an ordered sequence of helper equations;
- `false_model_search`: choose a finite-countermodel search route;
- `infinite_model`: research-only support for externally checked semantic
  countermodels.

The key design constraint is that the LLM is allowed to be creative but never
trusted. If it proposes a bad midpoint, the mechanical layer should reject it
with actionable feedback rather than silently accepting or discarding it.

## Useful Starting Points

- [System 1 / System 2 Protocol](system1_system2_protocol.md)
- [Mechanical / LLM Protocol v0](mechanical_llm_protocol_v0.md)
- [Research System Architecture](research_system_architecture.md)
- [Collaborative Solver Roadmap](collaborative_solver_roadmap.md)
- [LLM Midpoint Curriculum](llm_midpoint_curriculum.md)

## Current Status

The repository contains a compact public snapshot rather than the full private
workbench. Raw experiment transcripts, generated `.artifacts/`, and the upstream
Lean checkout are intentionally omitted. A small curated `evidence/` directory
contains sanitized summaries and end-to-end case studies for representative
LLM/mechanical interactions.

The main solver entry points are:

- `baby_solver.py`: maintained packed solver source;
- `scripts/compile_submission.py`: writes the generated competition
  `solver.py` under `.artifacts/compiled_submission/submission/`;
- `research_system/`: modular experimental framework for curriculum,
  blackboard, planner, executor, verifier, and feedback protocols.
