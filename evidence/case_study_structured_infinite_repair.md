# Structured Infinite-Model Repair and Distillation

This case study demonstrates a new false-side communication path: the
mechanical layer assembles a countermodel from typed parts, reports an exact
Lean failure for one bad part, and accepts an LLM repair without discarding the
parts that were already useful.

The result is deliberately modest. The infinite model was a checked-in known
fixture, and the experiment injected one typo. The meaningful claim is that the
repair and teacher-to-student replay are load-bearing and mechanically
verified, not that the LLM discovered the model from scratch or transferred it
to a different implication.

## Problem

The research curriculum case asks whether

```text
x ◇ y = (z ◇ (x ◇ y)) ◇ z
```

implies

```text
x ◇ y = z ◇ ((x ◇ y) ◇ z).
```

The implication is false in general but true in every finite magma. The
countermodel therefore uses carrier `ℕ`. Its structured source is
[`data/semantics/austin_3994_3588_infinite_model_plan.json`](../data/semantics/austin_3994_3588_infinite_model_plan.json).

The action contract separates:

- carrier and operation;
- reusable setup lemmas;
- the universal proof that the hypothesis holds;
- the concrete proof that the conclusion fails.

The mechanical assembler turns those parts into one `submission : Goal`. The
official research-profile Lean judge accepted the 865-byte assembled artifact.

## Injected Failure

The probe replaced `Nat.xor_comm` with the nonexistent
`Nat.xor_comm_typo` inside `hypothesis_proof`. Lean rejected the assembled
artifact and returned:

```text
Unknown constant `Nat.xor_comm_typo`
```

along with the remaining unsolved equality. The carrier, operation, range
lemma, and counterexample proof remained present in the parent action.

## LLM Repair

The bounded teacher search sent the parent action and exact Lean feedback to
`gpt-oss-120b`. The accepted child preserved the model and replaced the broken
hypothesis proof with a complete corrected fragment using `Nat.xor_comm`.
Mechanical assembly also repaired harmless outer tactic indentation. The
official judge accepted the resulting false certificate.

Trajectory minimization then removed the rejected parent attempt. Replaying the
single repaired action mechanically was still accepted. Its canonical action
SHA-256 is:

```text
547783819106c533a51e8b6c0e0c039e71e94915ff5c478dc360925a8df1e904
```

## Attribution Control

Two fresh ordinary-budget student runs used the same model and a two-round
budget:

| Student condition | Result | Attempts |
|---|---:|---:|
| No teacher lesson | rejected | 2 |
| Verified minimized lesson | accepted | 1 |

The lesson-aware student returned the minimized plan exactly, including all
mutually referenced Lean identifiers. The official research-profile judge
accepted it in 6.602 seconds. Because the no-lesson control failed, this is a
load-bearing exact-case student replay.

The machine-readable summary is
[`teacher_student_structured_models_2026_07_26.json`](teacher_student_structured_models_2026_07_26.json).

## What Remains

The next stronger milestone is held-out transfer: use a compact lesson about
repairing structured infinite models to improve a different implication. A
second frontier is model discovery, where the LLM proposes a useful carrier or
operation family rather than repairing a known one.
