# Case Study: `hard2_0027` Symbolic Countermodel

Date: 2026-07-27

## Result

`hard2_0027` is E1167 -> E1763:

```text
H: x = y ◇ ((z ◇ (y ◇ y)) ◇ x)
G: x = (y ◇ z) ◇ ((x ◇ z) ◇ x)
```

The implication is true for every finite magma but false for unrestricted
magmas. Finite tables, formula-defined finite models, CP-SAT, and larger
`Fin n` searches are therefore prohibited for this case.

The repository now contains an official-judge-accepted infinite certificate:

- readable Lean:
  `data/semantics/hard2_0027_modified_parity_model.lean`;
- structured six-part plan:
  `data/semantics/hard2_0027_modified_parity_model_plan.json`;
- packed single-file cache:
  `VERIFIED_SYMBOLIC_MODEL_ARTIFACTS_ZLIB_HEX` in `baby_solver.py`.

The assembled structured plan is 7,127 bytes. The readable certificate is
7,478 bytes and is accepted under the competition proof policy, not only the
research profile.

The compiled single-file solver replayed the verified certificate through the
official pipeline in 7.2 seconds with one judge call and zero LLM calls.

## Model

The carrier is `Nat`. Let `parity` toggle a Boolean on every successor. Define

```text
x ◇ y = succ y    when parity x = parity y
x ◇ y = pred y    otherwise
```

with the natural-number boundary patch `pred 0 = 0`.

The proof establishes:

1. parity is unchanged by two successors;
2. `a ◇ a = succ a`;
3. `a ◇ (a ◇ x) = x`;
4. `parity (z ◇ (y ◇ y)) = parity y`.

The last two facts prove H. The tuple `x = 0`, `y = 1`, `z = 0` refutes G.

## Provenance

The construction was traced to the dual of `Equation1659_facts` in the
Equational Theories Project at commit
`7e276a2d05e84e3eef02432abfd0718e78f7abfa`.

The dual model satisfies E2000 and refutes E1721. The implication graph gives
E2000 -> E1167 and E1763 -> E1721, so the same model satisfies E1167 and
refutes E1763.

## Protocol Improvements

This case exposed and fixed general symbolic-model gaps:

- semantic routing now distinguishes explicit tables, symbolic finite models,
  and infinite models;
- audited finite-valid/general-false cases suppress both table and symbolic
  finite search;
- structured plans now support pre-model local definitions;
- compound carriers are parenthesized, so types such as `Fin 257`, `ZMod n`,
  and products assemble correctly;
- missing `operation` can be inferred from a local `op` definition;
- a local `def` is repaired to `let`;
- split tactic fragments after `:= by` are merged;
- patches can replace `definitions[i]` and `setup[i]`;
- every repair round receives the complete active plan;
- exact Lean line ranges identify failed and preserved components;
- the infinite-only lane suppresses conflicting ordinary tool advice.

A separate `Fin 257` projection-model probe was accepted without constructing
or submitting a 257-by-257 table. This confirms that `Fin n` is a carrier type,
not necessarily an explicit-table representation.

## LLM Attribution

Live `gpt-oss-120b` probes without the verified lesson selected an infinite
structured plan, but proposed an invalid operation. Mechanical normalization
repaired its missing operation field and split setup block, and a subsequent
LLM call returned a correctly scoped indexed patch after the lane was made
exclusive.

The current model did not rediscover the parity construction, even after a
compact strategy lesson; it substituted unrelated operations. Therefore this
is a mechanical/research-derived solve and a verified-memory replay, not a
load-bearing LLM discovery.

That negative result is useful: the consumer, repair protocol, and certificate
format can handle the construction, while current-model strategy uptake remains
the bottleneck. A stronger future model can use the same interface without any
change to the trust boundary.
