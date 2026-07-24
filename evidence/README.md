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
- `case_study_hard1_0009_false.md`: end-to-end false-side route-selection case.
- `cases/*.json`: machine-readable versions of the case studies.
- `lean/*.lean`: Lean certificates accepted by the official Stage 2 judge for
  the showcased cases.

## Reading The Claims

The LLM is never trusted. In these examples it selects a midpoint, helper chain,
or search route. The mechanical layer must prove proposed helpers, find or
validate finite tables, render Lean, and pass the official judge. A case counts
as load-bearing only when the accepted judge attempt is attributed to an
LLM-selected action rather than to an earlier native route.
