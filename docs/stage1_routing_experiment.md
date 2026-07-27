# Stage 1 Prior and Feedback Routing Experiment

Date: 2026-07-27

## Question

Can the Stage 1 structural prompt become a useful true/false scheduler, and
does adding the current mechanical failure feedback improve that decision?

This experiment tests scheduling, not untrusted verdict acceptance. Every LLM
response selects one bounded action. Any resulting proof or countermodel is
still checked by the official Lean verifier.

## Design

The fixture contains ten deliberately difficult residuals: five true and five
false. Every case first receives the same cheap probes:

- true: two proof-battery layers plus a bounded equality graph;
- false: carrier-4 goal-directed model finding plus a `2x2` skew family;
- neither probe solves any fixture case.

The tested arms use the same model (`gpt-oss-120b` through OpenRouter),
temperature 0, a 12-second mechanical action cap, and the same Stage 1
features. The hidden answer is never included in a prompt.

1. `stage1_only`: Stage 1 strict rules and the M/S/V/C1/C2 prior, without
   attempt feedback.
2. `stage1_feedback`: the same prompt plus raw true- and false-probe states.
3. `stage1_feedback_calibrated`: the same feedback, with explicit warnings
   that fixed continuation recommendations are not verdict evidence and that
   a goal repeated as a midpoint is invalid.

The fixed TRUE-first baseline and deterministic Stage 1 tree each classify
5/10 fixture cases correctly.

## Results

| Arm | Parsed | Correct wing | True correct | False correct | Judge accepted |
| --- | ---: | ---: | ---: | ---: | ---: |
| Fixed TRUE-first | n/a | 5/10 | 5/5 | 0/5 | n/a |
| Deterministic Stage 1 | n/a | 5/10 | 4/5 | 1/5 | n/a |
| Stage 1 only | 10/10 | 5/10 | 4/5 | 1/5 | 1 |
| Stage 1 + raw feedback | 9/10 | 4/10 | 1/5 | 3/5 | 2 |
| Stage 1 + calibrated feedback | 10/10 | 5/10 | 4/5 | 1/5 | 1 |

The raw-feedback arm produced accepted certificates for:

- `hard2_0126` on the TRUE wing via `forward_saturation`;
- `hard1_0009` on the FALSE wing via `skew_product:2x3`.

The Stage-1-only and calibrated arms each accepted `hard2_0093` via the false
skew route.

An earlier full run, before adding the concise strict-TRUE reminder and the
calibrated arm, gave the same aggregate routing result: 5/10 without feedback
and 4/10 with raw feedback. Its raw-feedback arm also doubled accepted actions
from one to two, although the second accepted case differed. This suggests
that action diversity is real while the particular selection remains fragile.

Raw records, including prompts, model responses, normalized actions,
mechanical states, and verifier results, are generated under:

```text
.artifacts/stage1_routing_openrouter_v2.json
```

Reproduce the experiment with:

```bash
python3 scripts/stage1_routing_probe.py \
  --config configs/openrouter_gpt_oss_120b.example.json
```

## Diagnosis

The current telemetry is useful within a wing but is not calibrated for
choosing a wing:

- `recommended_next_call` after the false probe is a fixed continuation
  policy. The model incorrectly treats its presence as FALSE evidence.
- The true graph's closest pair can be the entire goal. The model sometimes
  returns that as a midpoint even though it does not split the obligation.
- Failure at carrier 4, failure of one `2x2` family, and disconnected equality
  components are all weak evidence. None estimates comparative progress in a
  common scale.
- The Stage 1 fallback was calibrated on a broad classification distribution.
  Hard residuals are a selected population on which its bare-variable rule is
  wrong for four of five false cases.

Prompt warnings prevent the worst copying behavior, but then the model simply
falls back to the original 5/10 prior. The missing ingredient is
discriminative feedback, not another wording pass.

## Decision

Do not replace the scheduler with a one-shot Stage-1-plus-feedback verdict
router.

The promising use is narrower and still valuable: keep the Stage 1 score as a
cheap budget-ordering prior, then let feedback-aware LLM calls diversify the
next bounded action inside a guarded portfolio. This produced additional
accepted TRUE and FALSE certificates even though its binary routing accuracy
was worse. Failed choices remain harmless because all artifacts are verified.

Before promoting feedback to a global router, mechanical responses should
add implementation-independent evidence fields:

- `recommendation_basis`: fixed continuation or case-specific;
- `verdict_evidence`: none, weak, moderate, or conclusive;
- `search_exhaustiveness`: what finite region was completely excluded;
- `progress_delta`: change from the preceding attempt;
- `bridge_quality`: whether a proposed bridge is smaller than the goal;
- `comparability_class`: which other wing measurements it can be compared to.

A later router can learn from accepted and failed episodes using those fields.
Until then, feedback should schedule exploratory actions, not infer truth.
