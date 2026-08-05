# Evidence

This directory contains a small public evidence slice for the
LLM/mechanical-collaboration claims in the repository.

It is not a dump of raw `.artifacts/` or provider transcripts. Those raw files
are intentionally excluded because they are noisy, can contain private local
paths, and are not pleasant to review. The files here are curated derivatives:
they keep the problem, mechanical feedback shape, LLM action, mechanical
consumption result, and Lean judge outcome.

## Files

- `llm_contribution_audit_2026_07_16.json`: compact selected-run attribution
  summary. It records 8 true and 3 false accepted cases whose winning route was
  attributed to an LLM-selected hint or tool call.
- `case_study_hard3_0231_true.md`: end-to-end true-side helper-chain case.
- `case_study_hard3_0202_repair.md`: real false-route/over-strong-lemma
  failure trajectory repaired into a contraction midpoint, plus a reproducible
  normalization probe that accepts a specialized version of the same idea.
- `case_study_hard1_0009_false.md`: end-to-end false-side route-selection case.
- `case_study_structured_infinite_repair.md`: structured infinite-model
  assembly, exact Lean repair feedback, and load-bearing teacher-to-student
  replay.
- `case_study_hard2_0027_symbolic_countermodel.md`: accepted modified-parity
  infinite countermodel generalized into an equation-driven residue-family
  search with honest LLM/mechanical attribution.
- `residue_ray_countermodel_2026_07_27.json`: machine-readable clean-room
  discovery, generated certificate, fake-ID end-to-end acceptance, and one
  previously solved true-case scheduling regression.
- `case_study_recursive_bundle_countermodel.md`: quotient/fiber decomposition,
  sparse symbolic finite-model synthesis, and a live two-step repair ladder
  accepted by the official judge.
- `case_study_native_skew_hard1_0009.md`: native packed-solver
  quotient-by-fiber route that turns a 90-second residual into an accepted
  six-element countermodel, plus its factor-repair feedback.
- `teacher_student_structured_models_2026_07_26.json`: machine-readable finite
  teacher-search stop result and structured infinite-model attribution summary.
- `hard2_0027_symbolic_countermodel_2026_07_27.json`: machine-readable
  semantic classification, certificate hashes, official verification, and
  attribution for the modified-parity model.
- `recursive_bundle_countermodel_2026_07_26.json`: compact machine-readable
  record of the non-uniform bundle case.
- `native_skew_hard1_0009_2026_07_26.json`: before/after packed-solver
  measurements and the accepted compact countermodel.
- `cases/*.json`: machine-readable versions of the case studies.
- `lean/*.lean`: Lean certificates accepted by the official Stage 2 judge for
  the showcased cases.

## Reading The Claims

The LLM is never trusted. In these examples it selects a midpoint, helper chain,
or search route. The mechanical layer must prove proposed helpers, find or
validate finite tables, render Lean, and pass the official judge. A case counts
as load-bearing only when the accepted judge attempt is attributed to an
LLM-selected action rather than to an earlier native route.
