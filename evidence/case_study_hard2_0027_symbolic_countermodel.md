# Case Study: Equation-Driven Symbolic Countermodel

Date: 2026-07-27

## Problem

The motivating implication is `hard2_0027`, E1167 -> E1763:

```text
H: x = y ◇ ((z ◇ (y ◇ y)) ◇ x)
G: x = (y ◇ z) ◇ ((x ◇ z) ◇ x)
```

It holds in every finite magma but fails for unrestricted magmas. An ordinary
`Fin n` search can therefore never find a countermodel.

## Historical Construction

The first accepted certificate used a modified parity walk on `Nat`:

```text
x ◇ y = succ y    when parity x = parity y
x ◇ y = pred y    otherwise
```

with `pred 0 = 0`. Its readable Lean proof and structured plan remain in
`data/semantics/` as research evidence. An earlier packed solver recognized the
exact equation IDs and replayed a compressed copy of that proof. That path was
useful for validating the symbolic-model interface, but it was benchmark
memory rather than general solving and has been removed from `baby_solver.py`.

## Generalized Search

The replacement tool receives only H and G. It searches operations on `Nat`
of the form

```text
max(0, a*x + b*y + c)
```

using one coefficient triple when `x` and `y` have the same residue modulo
`m`, and another triple otherwise. No problem ID, semantic registry entry,
stored lesson, or cached certificate participates.

A live `gpt-oss-120b` call selected:

```json
{
  "kind": "tool_call",
  "tool": "residue_ray_countermodel",
  "moduli": [2],
  "a_values": [-1, 0, 1],
  "b_values": [-1, 0, 1],
  "c_values": [-1, 0, 1],
  "candidate_cap": 2000,
  "budget": 2
}
```

The mechanical search checked 56 parameter pairs in 0.045 seconds and found:

```text
same residue:      (a,b,c) = (0,1, 1)
different residue: (a,b,c) = (0,1,-1)
```

It independently found the goal-breaking assignment `x=0, y=1, z=0`.

## Proof Compiler

Finite-prefix agreement is not a certificate for an infinite model. The
mechanical side therefore converts the discovered operation to an isomorphic,
proof-friendly carrier `Bool × Nat`. The Boolean is the residue state and the
natural number is the unbounded level. The two left actions become explicit
finite-state involutions.

The generated 1.4 KB Lean artifact proves:

1. the operation depends only on the Boolean state of its left input;
2. every left translation is an involution;
3. the middle term `z ◇ (y ◇ y)` has the same Boolean state as `y`;
4. these properties imply H;
5. the mechanically discovered assignment refutes G.

The official competition verifier accepted the artifact with no axioms. An
end-to-end run used deliberately unrelated equation IDs, made one LLM call and
one judge call, and completed in 14.4 seconds. This establishes that the solve
does not depend on the benchmark identifier. A separately renamed and
orientation-reversed form of H also produced an accepted certificate.

The same structural checkpoint was also exercised on the previously solved
true case `hard2_0193`. It spent one exploratory LLM call, produced no false
certificate, and the existing true prover subsequently solved the problem in
25.1 seconds. This is the expected scheduling cost of enabling a broader
symbolic lane.

## Provenance

The mathematical construction was traced to the dual of
`Equation1659_facts` in the Equational Theories Project at commit
`7e276a2d05e84e3eef02432abfd0718e78f7abfa`.

The generalization, parameter search, `Bool × Nat` representation, protocol
feedback, and competition-compatible proof compiler are implemented locally.
The result should be attributed as an LLM-selected, mechanically searched and
Lean-certified symbolic-family solve, not as independent LLM discovery of the
underlying mathematical construction.

## Remaining Limits

The search language already contains more operations than this one example,
but the current proof compiler covers only a narrow involutive parity-walk
certificate class. A finite-prefix candidate outside that class is returned as
`prefix_candidate_uncertified`, together with H violations, a concrete
G-witness when available, and involution failures.

The next generalization target is to compile arbitrary finite-state ray
transducers on `Fin m × Nat`, followed by broader residue-controlled affine
rules. Promotion should require a held-out implication, not merely another
encoding of this case.
