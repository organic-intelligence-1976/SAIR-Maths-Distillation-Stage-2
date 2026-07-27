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

## 2026-07-26 Execution Checkpoint

The teacher platform is now implemented rather than only planned:

- mechanically ranked bounded beams with concurrent independent proposals;
- parent-action and exact failure feedback on every continuation;
- resumable beam checkpoints with full action lineage;
- finite carrier lower bounds from exact propagation probes;
- trajectory minimization by mechanical replay;
- ordinary-student no-lesson and with-lesson attribution controls;
- promotion only when mechanical replay and lesson-aware student replay pass
  while the no-lesson control fails.

The first long flat finite-family search on `hard2_0093` did not solve the case.
Exact propagation eliminated carrier sizes 2 through 5. At size 6 the teacher
produced a goal-breaking family with 9 hypothesis failures among 36 checked
assignments, but no countermodel. After 63 unique actions and 12 cumulative
depth levels, this lane hit its stop condition.

That consumer gap now has a first answer. Equal-fiber skew products found
countermodels for 27 of 60 hard-false cases lacking a simple invariant
separator. The non-uniform bundle extension then solved `hard2_0125` with a
two-element quotient, fiber sizes `[4,2]`, four affine local maps, and six
patched cells. A controlled live run began with a failed `2x2` skew family;
`gpt-oss-120b` followed the structured mechanical repairs through `[3,2]` and
`[4,2]`, and the final ordinary table passed the official judge. Compact
feedback now preserves `mechanical_status=family_infeasible`, and a bounded
correction reprompt handles ignored primary repairs. This is a verified
collaboration result, though `hard2_0125` was already solvable by broad
mechanical CP-SAT and the first skew action was deliberately seeded.

The equal-fiber constructor has since crossed the packed-solver coverage
boundary. A generic native `skew_product:QxF` false-search route solved
`hard1_0009`, which the prior packed solver missed at both 12 and 90 seconds.
The official judge accepted the six-element `2x3` expansion; the same
12-second 27-case audit moved from 25/27 to 27/27. A mechanically infeasible
`2x2` attempt emits `2x3` as the next protocol action. This is a native
mechanical win with useful System-2 feedback, not an LLM-attributed solve. See
[`../evidence/case_study_native_skew_hard1_0009.md`](../evidence/case_study_native_skew_hard1_0009.md).

The structured infinite lane did reach its first attribution milestone. A
known `ℕ` model was assembled from five typed parts and accepted by the official
research-profile judge. After injecting a broken theorem identifier into the
hypothesis proof, the teacher used exact Lean feedback to repair that part while
preserving the model, setup, and counterexample proof. A fresh ordinary model
failed twice without the verified lesson and passed in one round with it. See
[`../evidence/case_study_structured_infinite_repair.md`](../evidence/case_study_structured_infinite_repair.md).
This is exact-case distillation, not yet held-out transfer or model discovery.

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

Current status: platform complete; finite-false discovery milestone not yet
met. The `hard2_0093` run produced useful measured near-model progress and a
clear next consumer hypothesis, but no lesson was promoted.

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
The plan now includes pre-model local definitions, so an operation can depend
on symbolic helpers such as parity, residue classes, or fiber projections.

The existing whole-file artifact remains an expert fast path, but it must no
longer be the only interface. Research soundness and competition-policy
eligibility remain separate fields.

Promotion milestone: reconstruct one known infinite countermodel from
structured parts, repair at least one rejected obligation, and obtain a
judge-accepted final artifact.

Current status: the former exact-case replay has been retired from the
submission solver. For the motivating E1167 -> E1763 equations, live
`gpt-oss-120b` selects a general residue-controlled clamped-affine search;
the mechanical side rediscovers the parity walk in 56 candidates, compiles it
on `Bool × Nat`, and produces a competition-policy-accepted artifact. The
end-to-end run also succeeds under deliberately unrelated equation IDs.
The underlying construction still comes from published mathematics, and the
proof compiler currently covers only a narrow involutive parity-walk class.
Held-out equation-family transfer remains the next promotion gate.

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

1. Finish compiled-submission validation for the new contracts.
2. Add a mechanically assisted multiobjective repair operator for finite
   near-models, preserving both H progress and a concrete G-breaking witness.
3. Run the finite teacher on one fresh residual before returning to
   `hard2_0093`.
4. Test structured infinite-model lesson transfer on a distinct known
   construction.
5. Begin carrier/operation discovery prompts only after repair transfer is
   stable.
6. Promote midpoint attain/consume into explicit recursive graph nodes.
