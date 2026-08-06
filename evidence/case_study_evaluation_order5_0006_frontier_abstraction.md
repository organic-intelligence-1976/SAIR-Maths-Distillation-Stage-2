# Case Study: Abstracting A Large Proof Frontier

This order-five case records a load-bearing LLM repair and the regression gate
used before adopting it.

## Problem

```text
H    : x = (y ◇ ((z ◇ w) ◇ y)) ◇ (x ◇ y)
Goal : x = (y ◇ z) ◇ ((y ◇ (z ◇ y)) ◇ w)
```

## Failure

The previous prompt promoted a 32-node proof frontier as a mandatory first
midpoint. Across six healthy LLM calls, the model repeatedly copied that large
equation and appended both left and right projection. The first rung exhausted
the shared budget, while the two projections were competing alternatives rather
than an ordered dependency. No certificate was produced.

## Protocol Repair

The collaboration policy now distinguishes compact and large frontiers:

- a compact frontier may be used as an exact first rung;
- a large frontier is evidence from which repeated context should be removed;
- independent alternatives belong in `candidate_bundle`;
- `lemma_chain` is reserved for facts whose later rungs can use earlier ones;
- proved-but-unconnected rungs must be extended by a new bridge rather than
  merely resubmitted.

The policy is equation-structural. It contains no benchmark identifier or exact
problem equation.

## Accepted Trajectory

On the fresh run, the first true-side LLM action selected standard auxiliary
superposition. The mechanical response then exposed compact idempotence. The
next LLM call returned:

```json
{
  "kind": "tool_call",
  "tool": "lemma_chain",
  "target": "goal",
  "lemmas": [
    {"name": "idempotence", "equation": "a = a ◇ a"},
    {"name": "proj_l", "equation": "a ◇ b = a"},
    {"name": "collapse", "equation": "a = b"}
  ]
}
```

The mechanical consumer independently proved every rung, stitched the final
goal, and obtained acceptance from the official local Lean proxy. The run used
three successful LLM calls and twelve judge calls in 218.633 seconds.

## Regression Gate

The compiled solver then passed a risk-ranked 20-case set containing 11 true
and 9 false implications. The set included LLM-repair cases, grind-sensitive
proofs, deep true certificates, exact finite countermodels, and the symbolic
countermodel route. All 20 produced accepted Lean certificates with no label
mismatches.

The result is therefore a collaboration gain, not a replacement of prior
mechanical coverage.
