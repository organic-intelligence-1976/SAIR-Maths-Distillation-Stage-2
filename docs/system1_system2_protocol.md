# System 1 / System 2 Protocol

See `docs/mechanical_llm_protocol_v0.md` for the precise v0 schema. This file
keeps the higher-level design notes and historical framing.

This project is converging on a two-system architecture.

- **System 1** is the trusted mechanical layer, mostly driven by the reference baseline's
  engines: graph search, superposition, certificates, model finding, and proof
  rendering.
- **System 2** is the strategist, mostly driven by this project's LLM loop: tool
  selection, midpoint suggestions, lemma chains, model-search routes, and repair
  proposals.
- **The protocol** is the adapter between them. It translates LLM output into
  bounded mechanical requests, and translates mechanical progress/failure into
  LLM-readable state.

The soundness boundary is always System 1 plus the Lean judge. System 2 output
is never trusted; it only chooses what System 1 should try.

## Versioned Baselines

To measure whether System 2 helped, freeze a tuple:

```text
M_vN = mechanical engines and proof/model renderers
P_vN = protocol adapter and telemetry contract
S_vN = strategist prompt, examples, tool-ranking, and repair policy
```

A load-bearing System 2 win is:

```text
(M_vN, P_vN) fails
(M_vN, P_vN) + hint/route from S_vM succeeds
```

If the successful hint is later distilled into `M_vN+1`, that is not evidence
that System 2 was useless. It is evidence that the flywheel worked.

## What Freezing Means

For a specific comparison, freeze:

- available tools;
- their mathematical capabilities;
- their budgets and scheduling rules;
- accepted input schemas;
- proof/model rendering behavior.

It is still fine to improve non-mathematical presentation separately, but those
changes should get their own protocol version when they affect outcomes.

Protocol-only changes:

- clearer `SearchState` summaries;
- less noisy term formatting;
- better classification of parse errors, timeouts, and failed hints;
- JSON field names that are easier for the LLM to use.

System-1 changes:

- new theorem-proving strength;
- new finite-model search strength;
- hardcoded proof templates;
- stronger proof renderers;
- different search budgets or route ordering.

Gray-zone changes should be versioned explicitly. Examples include syntax
repair, variable canonicalization, and filling in obvious missing arguments.

## Tool Contract

Each System 1 module should be exposed as a tool with the same broad shape:

```json
{
  "tool": "name",
  "input": {
    "h": "universal hypothesis",
    "target": "goal or midpoint",
    "assumptions": ["already proved helper lemmas"],
    "budget": 8
  },
  "output": {
    "status": "proved | found_model | stuck | refuted | timeout",
    "proof_body": "Lean tactic body if proved",
    "counterexample_table": "finite magma table if found",
    "state": {
      "proved_facts": [],
      "generated_equations": 0,
      "closest_equations": [],
      "left_frontier": [],
      "right_frontier": [],
      "failed_hints": [],
      "need_hint": {}
    }
  }
}
```

The exact fields can vary by module, but every failure should answer:

```text
What did you try?
What did you prove or generate?
Why did the current request fail?
What kind of next hint would be useful?
Which exact repeated attempts should be avoided?
```

## Import Rule

Import the reference mechanical baseline engines, not the reference mechanical baseline orchestration wholesale.

Good import:

```text
the reference mechanical baseline superposition core
→ bounded `goal_superposition` tool
→ proof body or `SuperpositionState`
```

Risky import:

```text
the reference mechanical baseline entire fallback sequence
→ hidden default behavior
→ no clear accounting for LLM contributions
```

The goal is not to keep System 1 weak. The goal is to keep the boundary visible
so System 2 can still help at the current frontier.

## Current Baby-Solver Pattern

`baby_solver.py` now uses this pattern in four places:

- generic midpoint/lemma chains: LLM proposes equations, System 1 proves each
  helper and then consumes it;
- proof-carrying superposition: the reference baseline's core is exposed as
  `goal_superposition` and as a fallback consumer for helper lemmas;
- standard auxiliary superposition: baseline-style `const`, projection, and
  row-constant lemmas are exposed as explicit tool targets, with small-model
  refutation before proof search and structured failure state if no helper is
  both proved and consumed;
- false-model search: LLM proposes routes, System 1 checks tables or emits
  per-route model-finder/local-search state.

The LLM prompt also has a `strategy_cards` layer. A card is not trusted proof
content; it is an LLM-facing routing hint with a concrete protocol action. For
example:

```json
{
  "name": "generalize_goal_to_right_projection",
  "principle": "If G is a special instance of a simpler universal law, try the universal law first.",
  "recommended_action": {
    "kind": "tool_call",
    "tool": "standard_aux_superposition",
    "lemmas": ["proj_r"]
  }
}
```

This lets System 2 use high-level proof wisdom while System 1 still owns all
mathematical work. The current implemented cards cover direct projection
instances, nested projection collapse, same-left/same-right constancy, square
terms, and the pattern "rewrite with H once, then rowconst".

The same layer now also consumes false-search telemetry. False-side cards:

- preserve failed native `false_model_search` states for later LLM passes;
- expose exact `recommended_next_call` routes as first-class actions;
- treat CP-SAT `UNKNOWN` as "continue exact search with more budget / next
  carrier" rather than as ordinary failure;
- repair stale or empty LLM false-search calls to the top false continuation
  during false-focused phases, while preserving fresh untried LLM routes even
  when they differ from the mechanically top-ranked card;
- carry failed LLM false-search routes from the pre-child collaboration pass
  into the final fallback pass, so the outer loop does not rediscover the same
  failed route sequence;
- suppress/repair generic projection and constant midpoint hints during a
  false-telemetry phase when a concrete false continuation is available.

This improved the `hard2_0027` handoff but did not solve the case. The current
diagnosis is that System 2 can now steer to the relevant CP-SAT continuations
and then local-search continuations without cycling through stale routes; System
1 still lacks enough finite-model reach on that problem.

A later false-route checkpoint made this load-bearing on easier false cases:
after focused true tools and goal-directed false search fail, System 2 gets one
false-focused route-selection pass before the native late portfolio. The
critical protocol lesson was not to over-normalize. `hard1_0009`, `hard2_0016`,
and `hard2_0093` now have runner-attributed `llm:false_model_search` accepts
because fresh untried LLM-selected routes are executed rather than replaced by a
mechanically preferred continuation card.

One candidate false-side extension is symbolic or piecewise counterexample
families. This belongs on the protocol boundary, not inside the trusted core at
first:

```json
{
  "kind": "false_model_family",
  "carrier_size": 20,
  "operation": {
    "default": "affine | projection | residue_class | piecewise",
    "rules": []
  }
}
```

System 2 may propose such a family, but System 1 must expand or evaluate it and
return ordinary verifier-facing facts: whether `H` holds universally, whether
`G` fails somewhere, which assignments/cells break, and whether a compact Lean
certificate can be rendered. The first experiment showed that arbitrary sparse
patches around projection defaults are too weak/noisy for `hard2_0027`; future
attempts should ask for structured families such as parity classes,
diagonal/off-diagonal laws, affine regions, or other compact finite-model
schemes.

The next imports should continue this pattern: one reference module at a time,
wrapped as a bounded tool with structured feedback.
