# Verified Teacher-Student and Symbolic Model Plan

Status: active execution plan, 2026-07-26

## Objective

Build the collaboration layer so that a stronger or higher-budget language
model can discover proof and countermodel strategies that the ordinary
submission model can later reuse at lower cost. Every discovery remains
untrusted until the mechanical consumer and Lean judge verify it.

The target flywheel is:

```text
sample an unsolved frontier case
-> run a stronger/broader System-2 search
-> mechanically verify every proposed action
-> minimize the accepted trajectory
-> distill the decisive strategy
-> replay with the ordinary model and ordinary budget
-> test transfer on structural siblings
-> retain, retrieve, coalesce, or reject the lesson
```

Teacher runs may increase model strength, proposal count, and LLM rounds. The
per-action mechanical consumer should remain close to the submission contract.
This keeps the harvested lesson about choosing a better action instead of
silently buying a much larger standalone mechanical proof.

## Phase 1: Finite Symbolic Countermodel Families

Promote `false_model_family` from a research sidecar to a first-class solver
action. A proposal describes a finite carrier and a compact operation family,
not an unverified verdict:

```json
{
  "kind": "false_model_family",
  "carrier_size": 12,
  "default": {"kind": "affine", "params": [1, 0, 0]},
  "rules": [
    {"when": {"kind": "diagonal"}, "value": "i + 1"}
  ]
}
```

The mechanical consumer must:

1. validate and normalize the family schema;
2. expand it to an ordinary finite operation;
3. check H universally and find at least one G-breaking assignment;
4. return structured near-miss feedback when it fails;
5. render an ordinary finite Lean certificate when it succeeds;
6. count the result only after the official judge accepts it.

Near-miss feedback should include H-violation examples, G-breaking examples,
hot operation cells, carrier size, operation-family summary, and whether the
candidate is sterile (H holds but G never fails) or promising (G fails but H
still has repairable violations).

Promotion milestone: one production contract case accepts a proposed family,
one failed family returns actionable diagnostics, and compiled-submission smoke
tests remain green.

## Phase 2: Teacher Search and Student Replay

Add a frontier-harvesting harness with four outcomes:

- `teacher_unsolved`: retain the failure signature for platform-gap clustering;
- `teacher_solved_not_distillable`: keep the verified episode as research
  evidence, but do not spend production prompt context on it;
- `student_replay`: the ordinary model reproduces the accepted strategy under
  the target budget;
- `heldout_transfer`: the lesson improves a distinct structural sibling.

Prefer a bounded beam over one long conversation. At each state, obtain several
independent actions, execute them mechanically, retain the best verified or
partial states, and continue only those branches. Keep a random exploration
fraction, but stratify most sampling across verdict, variable width, structural
family, and mechanical failure signature.

Promotion milestone: at least one finite-false teacher discovery becomes a
load-bearing normal-budget student solve, with a no-lesson counterfactual.

## Phase 3: Retrieval and Coalescing

Maintain three separate artifacts:

1. immutable verified episodes;
2. compact lessons of the form trigger -> action -> feedback -> repair;
3. generalized strategies supported by multiple lessons.

Retrieve only a small number of lessons matching the current semantic and
mechanical state. Periodically cluster examples by normalized action,
countermodel family, failure signature, and repair mechanism. A coalesced
strategy replaces examples only after held-out replay shows equal or better
coverage at the same context budget.

Use prompt ablation to remove examples with no marginal verified value. Exact
case memorization may remain in the evidence store but is not a production
strategy.

Promotion milestone: compact retrieval matches or exceeds raw-example
retrieval on a held-out multi-family slice while using less context.

## Phase 4: Structured Infinite Countermodels

Replace the whole-file-only infinite action with a parameterized obligation
plan:

```text
carrier definition
-> operation definition
-> closure/type obligations
-> universal proof that H holds
-> concrete assignment where G fails
-> final Lean assembly
```

Each obligation becomes persistent state. Accepted definitions and lemmas
survive later repair rounds; rejected Lean fragments return exact diagnostics.
Begin with known closed infinite countermodels before attempting
`hard2_0027`/E1167 -> E1763.

The existing whole-file artifact remains an expert fast path, but it must no
longer be the only interface. Research soundness and competition-policy
eligibility remain separate fields.

Promotion milestone: reconstruct one known infinite countermodel from
structured parts, repair at least one rejected obligation, and obtain a
judge-accepted final artifact.

## Phase 5: Explicit Recursive Obligations

Promote midpoint attain and consume legs from the packed worker into persistent
nodes:

```text
attain:  H + proved facts -> M
consume: H + proved facts + M -> G
audit:   assembled proof -> Lean acceptance
```

A blocked attain or consume node may request a new midpoint and create child
obligations. The same graph machinery should represent finite-family fitting
and infinite-model construction. Budgets, proved facts, refutations, and
reopen-novelty evidence remain local to each node.

Promotion milestone: a case fails with one midpoint, succeeds after a child
midpoint is introduced on a blocked leg, and the final nested proof verifies.

## Continuous Guardrails

- Never promote an unverified LLM claim.
- Preserve raw evidence separately from compact lessons.
- Require attribution: the lesson must change failure into acceptance.
- Test alpha-renamings, orientations, duals, and structural siblings.
- Track teacher compute, student compute, mechanical compute, and judge calls
  separately.
- Repeated teacher failures with the same signature become platform work
  rather than disappearing when sampling moves to another case.
- Prefer protocol or consumer improvements over hardcoded case identifiers.

## Immediate Execution Order

1. Wire finite `false_model_family` through the production tool contract.
2. Add successful and failed-family contract fixtures and prompt examples.
3. Run compiled-submission and official-proxy smoke tests.
4. Build the first teacher/student finite-family probe.
5. Generalize infinite artifacts into persistent construction obligations.
6. Promote midpoint attain/consume into explicit recursive graph nodes.
