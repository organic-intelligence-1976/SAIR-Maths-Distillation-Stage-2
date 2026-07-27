# Native Quotient-By-Fiber Countermodel: `hard1_0009`

This case demonstrates a compact symbolic model family becoming a native
single-file submission route. It is a mechanical coverage win with
LLM-consumable feedback, not a load-bearing LLM solve.

## Problem

```text
H: x = ((x ◇ x) ◇ (y ◇ z)) ◇ y
G: x = ((x ◇ (y ◇ x)) ◇ x) ◇ y
```

The implication is false.

## Previous Packed Result

At a 12-second solver cap, the packed solver timed out after one rejected true
certificate. At 90 seconds it still timed out after seven rejected true
certificates and one LLM call. No accepted false route was reached.

## Compact Search Language

The new `skew_product:2x3` route represents each carrier element as `(q, f)`:

- `q` belongs to a synthesized two-element quotient;
- `f` belongs to a three-element fiber;
- each quotient operation cell selects one affine map
  `a * left + b * right + c (mod 3)` for the fiber operation.

By default the quotient must satisfy both H and G. Therefore, a target
separation in the six-element expansion is genuinely created by the fiber
extension rather than inherited from a smaller quotient countermodel.

The approved competition image does not include OR-Tools, so the packed route
has a dependency-free backend that enumerates low-description-complexity maps
first. When OR-Tools is available, CP-SAT plus a CEGIS loop accelerates the
same search language. Both backends return a candidate only after exhaustive
mechanical evaluation confirms H universally and finds a concrete failure of G.

## Result

The native packed solver found this six-element table:

```text
[[2,2,2,2,2,2],
 [0,0,0,0,0,0],
 [1,1,1,1,1,1],
 [3,5,4,4,4,4],
 [5,4,3,5,5,5],
 [4,3,5,3,3,3]]
```

The official Stage 2 Lean judge accepted the resulting `Fin 6` certificate.
With OR-Tools forcibly disabled to simulate the approved solver image, the
fixed 12-second run finished in 6.88 seconds with one judge call and no LLM
calls. Across the 27-case compact-model candidate sweep, coverage moved from
25/27 to 27/27 with no losses. The optional OR-Tools accelerator completed the
single case in 5.50 seconds.

## Feedback Contract

The route is exposed through the ordinary `false_model_search` protocol:

```json
{
  "kind": "tool_call",
  "tool": "false_model_search",
  "routes": ["skew_product:2x3"],
  "budget": 4
}
```

On this problem, `skew_product:2x2` is mechanically infeasible. Its structured
state recommends `skew_product:2x3`, which then succeeds. This gives System 2 a
meaningful operation over the search language: change the factorization in
response to an eliminated family, rather than guessing individual table cells.

## Attribution

This result should be counted as:

- a new packed-solver false-side coverage win;
- a native compact symbolic constructor;
- a successful mechanical-to-LLM feedback surface.

It should not be counted as an LLM solve, because the early native scout found
the model before an LLM action became load-bearing.

Machine-readable evidence is in
[`native_skew_hard1_0009_2026_07_26.json`](native_skew_hard1_0009_2026_07_26.json).
