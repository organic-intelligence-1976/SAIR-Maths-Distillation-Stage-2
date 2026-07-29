# E Proof-Trace Teacher Experiment

## Purpose

This experiment tests a cheaper alternative to adding another recursive LLM
level on difficult true implications. A mature equality prover supplies an
untrusted ordered plan, while the existing proof-carrying mechanical layer
reconstructs every edge and the official Lean judge checks the stitched result.

E is a research teacher here, not a trusted verifier and not a submission
dependency. No TSTP clause is accepted merely because E emitted it.

## Mechanism

[`scripts/eprover_trace_replay_probe.py`](../scripts/eprover_trace_replay_probe.py)
parses positive unit equations and their parent references from a TSTP trace.
For every proposed helper it tries:

1. parent-local proof-carrying saturation;
2. explicit normalization of nested `spm` plus `rw` inferences;
3. a bounded linear parent replay for repeated-occurrence rewrites;
4. the existing broad mechanical consumer as a fallback.

Every successful helper becomes a normal Lean `have`. Rewrites are rendered
with `congrArg` and equality transitivity. The final competition goal is then
proved from the accumulated helpers and checked through
`OfficialLeanVerifier`.

## Results

| Problem | Trace target | Helpers | Official result | End-to-end time |
| --- | --- | ---: | --- | ---: |
| `hard3_0214` | original goal | 10 | accepted, no axioms | 4.2 s |
| `hard3_0314` | right projection | 19 | accepted, no axioms | 10.9 s |

The accepted bodies and detailed reports are generated under `.artifacts/`:

- `hard3_0214_eprover_replay.leanbody`
- `hard3_0214_eprover_replay.json`
- `hard3_0314_eprover_replay.leanbody`
- `hard3_0314_eprover_replay.json`

These files are intentionally research artifacts rather than committed
problem-specific solver data.

## What We Learned

The earlier recursive midpoint probe selected left projection for
`hard3_0214`. E's saturation showed that this stronger statement is not a
consequence of the hypothesis, even though the original goal is. More LLM
budget spent proving that midpoint could not succeed.

The broad consumer could prove many individual trace clauses but missed
several locally simple edges because it searched a much larger equation pool.
Named parent references changed the problem substantially:

- E's simultaneous superposition sometimes became two or more ordinary
  `congrArg` rewrites.
- A nested rewrite step on `hard3_0314` normalized in four explicit rewrites.
- Once those local edges were reconstructed, the existing final consumer
  closed both original goals quickly.

The useful capability is not "call E" or "hardcode these traces." It is:

> Consume a longer ordered lemma plan whose steps name the previously proved
> parents they expect to use, and return edge-local feedback when replay fails.

## Promotion Path

The next production-facing step is to extend the LLM/mechanical action
contract with an ordered proof-plan form:

```json
{
  "kind": "ordered_lemma_plan",
  "steps": [
    {
      "name": "bridge_1",
      "equation": "...",
      "parents": ["h"]
    },
    {
      "name": "bridge_2",
      "equation": "...",
      "parents": ["bridge_1", "h"]
    }
  ]
}
```

The consumer should replay each step against only its named parents first,
retain the current trusted broad prover as fallback, and report the first
unreconstructed edge. E traces can then generate offline curriculum examples
for this protocol, while a live LLM can propose or repair the same plan form.

This should precede full recursive LLM calls for these cases. Recursion remains
useful when no coherent plan is available, but it is not required to validate
or consume a good multi-rung plan.

## Promotion Result

The lesson was promoted without adding E as a runtime dependency. The packed
solver now exposes `ordered_completion`, a pure-Python scheduler over the
existing proof-carrying paramodulation machinery. It:

1. orients and simplifies equations while prioritizing a requested helper;
2. retains the parent and normalization dependency graph;
3. replays only the target's dependency closure;
4. reports the first edge that cannot be reconstructed; and
5. asks the official Lean judge to validate the final stitched certificate.

The native route derives row constancy for the former `hard3_0214` residual and
right projection for the former `hard3_0314` residual. A fresh full-corpus run
of the compiled one-file submission produced:

- 1,669 solved problems out of 1,669;
- 1,669 retained Lean certificates;
- 819 true and 850 false verdicts;
- zero expected-answer mismatches; and
- zero unresolved problems.

The audit summary is generated at
`.artifacts/full_verification_native_completion_20260728/summary.json`. The
artifact directory is intentionally uncommitted; this document records the
reproducible command and result, while `scripts/run_full_verification.py`
regenerates the complete evidence.
