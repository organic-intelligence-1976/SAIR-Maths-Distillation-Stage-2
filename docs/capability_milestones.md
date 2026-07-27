# Capability Milestones

This file defines progress at the protocol boundary. Milestones should say what
System 1 and System 2 can do together, not which internal lemma family happened
to prove it. Concrete lemma families remain evidence examples only.

## Grading Rule

- C means there is a plausible mechanism or one isolated example.
- B means the mechanism has verified evidence, but either breadth, live uptake,
  or repeatability is still thin.
- B+ means the capability is reliable enough to stop pushing it for now and move
  to the weakest remaining surface.
- A is reserved for broad coverage evidence, not for the current flywheel.

When a capability reaches B+, new work should move elsewhere unless a regression
appears or the capability blocks another below-B+ item.

## Surfaces

| Surface | B+ milestone | Current grade | Evidence examples | Next action |
|---|---|---|---|---|
| Boundary contract and normalization | LLM actions, tool calls, false-search requests, and malformed-but-guessable outputs normalize to a stable protocol object; unsupported actions return actionable registry feedback; packed solver passes true/false smoke. | B+ | Protocol-v0 adapter, tool registry, packed 2-case smoke. | Stop unless a new tool breaks the contract. |
| Mechanical consumption of external help | Given externally supplied reusable midpoints or lemma chains, the mechanical side proves and stitches at least 8 diverse true cases; incomplete or bad hints fail safely; all accepted bodies are judge-verified. | B+ | `.artifacts/midpoint_curriculum_verified_v4.json` has 10/10 good repairs accepted and all bad guesses rejected. | Stop; add only new evidence families from discovery. |
| True-side LLM reach extension | Live LLM feedback repair produces judge-accepted proof bodies on at least 4 true cases across at least 3 abstract failure modes, with the mechanical side independently verifying every hint. | B+ | Live repairs for held-out opconst-style midpoint, multi-lemma sandwich, proved-but-unused helper, projection-pair/too-specific-midpoint, and `hard3_0202` row-context contraction failures. | Stop broad prompt work; mine only genuinely new failure modes. |
| Multi-rung helper planning | At least 3 cases require more than one helper or a repaired helper chain; single-helper or incomplete-chain attempts fail; live LLM selects a successful chain on at least 2 cases. | B+ | v4 curriculum plus live chain repairs on square-sandwich, rowconst-to-opconst, and projection-pair cases. | Stop except for attribution cleanup. |
| False-side route collaboration | After a failed finite-search route, the mechanical side emits non-stale route feedback; live LLM selects a non-redundant continuation on at least 2 false cases; at least 2 selected continuations verify as accepted countermodels. | B+ | `hard1_0009` live repair accepted; `hard2_0016` live uptake chose a new route and `.artifacts/feedback_uptake_hard2_0016_execute_v1.json` verified the selected countermodel. | Stop routing work; next false-side work must strengthen the consumer for currently unsolved cases. |
| Measurement and attribution discipline | A reproducible report maps artifacts to these capability milestones and separates accepted mechanical, LLM-assisted, false-route, and unsolved evidence without relying on implementation-family names as milestone labels. | B+ | `scripts/capability_milestone_report.py` generates `.artifacts/capability_milestone_report.{json,md}`. | Use after focused sweeps; avoid hand-edited grade drift. |
| External mechanical module import | At least one true-side and one false-side baseline-style mechanism is exposed through the same tool/feedback contract, individually attributed, and not counted as a hidden monolithic fallback. Full reference mechanical parity is an A-level goal, not B+. | B+ | Contracted imports include true-side superposition/aux/proof-battery/grounding tools plus false-side model-finder, reference mechanical counterexample, and optional `cp_sat` routes; representative artifacts exist for each wing. | Stop broad import work; next import should be justified by a new child-only or frontier-only gap. |
| Hard false-case consumption | With the LLM already selecting reasonable routes, System 1 can turn at least one previously unsolved hard false focus case into an accepted countermodel under fixed budget. | Strong B+ | `hard2_0093` has an accepted size-6 table, `hard2_0125` is accepted by CP-SAT, and the finite-valid `hard2_0027` equations are now solved by an LLM-selected residue-ray family plus a mechanically generated infinite Lean certificate. | Require a held-out symbolic-family solve before calling this A-level generalization. |

## Evidence Naming

Milestone names should not mention implementation-specific helper families.
Evidence rows may mention them because reproducibility needs exact artifacts.
For example:

- Capability: repair a proved-but-unused helper.
- Evidence: a row-shaped helper repaired by a stronger product-collapse helper,
  or a one-sided projection repaired by adding the opposite projection.

That split preserves the architecture goal: System 1 and System 2 can improve
independently as long as they honor the protocol boundary.
