# Stage 2 submissions

The four solver artifacts submitted to the SAIR Mathematics Distillation
Challenge (Equational Theories, Stage 2), one per track-and-model slot. Each is
a single self-contained `solver.py`-contract file (≤ 500,000 bytes, no
`exec`/`eval`/`compile`) that emits Lean 4 certificates for the deterministic
judge. The competition allows two submissions per track; we used both slots per
track, one tuned for each evaluation model.

| File | Track | Model | Bytes | sha256 (first 16) |
|---|---|---|---|---|
| `solver.py` | Solo | google/gemma-4-31b-it | 498,778 | `199897e918508ef7` |
| `solo_gpt-oss.py` | Solo | openai/gpt-oss-120b | 498,778 | `148a28eff4b0bf99` |
| `marathon_solver.py` | Marathon | google/gemma-4-31b-it | 499,672 | `62212b965ed9d7d8` |
| `marathon_gpt-oss.py` | Marathon | openai/gpt-oss-120b | 499,961 | `fa7f221db46ca3a9` |

## Design notes

- **Mechanical first, LLM as backstop.** The vast majority of solved problems
  are certified with zero LLM calls by a mechanical core (collapse detection,
  witness-grounding, superposition, congruence closure). The LLM is engaged only
  after the mechanical routes exhaust, and its proposals are always verified
  before use.
- **Solo** runs one problem per subprocess with an interactive judge: it can
  attempt a certificate, read the judge's response, and retry.
- **Marathon** runs many problems under a global budget with no interactive
  judge (certificates are scored post-hoc). To compensate, the Marathon builds
  carry a self-contained soundness layer: a pure-Python proof checker that
  verifies our own TRUE certificates before committing them, proof-producing
  congruence closure that renders opaque `grind` successes as explicit
  checker-verifiable calc chains, and bank-then-upgrade emission so a timeout
  can never lose a problem. The `_gpt-oss` Marathon build adds a second pass that
  revisits any problem left unsolved after the first pass with a larger budget.
- **Per-model tuning** differs only in the parts that interact with the
  evaluation model (LLM-engagement thresholds); the mechanical core is shared.

## Provenance and credits

All certificate scaffolding targets the SAIR Foundation's official Stage 2
judge/proxy/runner. Equation numbering and the law corpus come from the
Equational Theories Project (Terence Tao et al.). TRUE-side certificates rely on
Lean 4 / Mathlib's `grind`. Ideas adopted from the public SAIR Stage 2
contributor network are credited in the repository's top-level
[`CREDITS.md`](../CREDITS.md).
