# Approach-Family Obligation Graph v1

Status: working vertical slice, 2026-07-20

The modular research runtime now accepts a `proof_plan` action containing
family-labeled lemma nodes, AND dependencies, OR-group annotations, mechanisms,
and the root obligation each node advances.

Example:

```json
{
  "kind": "proof_plan",
  "nodes": [
    {
      "id": "square_absorb",
      "equation": "u ◇ (v ◇ v) = v",
      "family_id": "square_normalization",
      "mechanism": "derive a square normal form",
      "alternative_group": "root_route",
      "depends_on": []
    },
    {
      "id": "right_square",
      "equation": "u ◇ v = v ◇ v",
      "family_id": "square_normalization",
      "mechanism": "strengthen the normal form",
      "depends_on": ["square_absorb"]
    }
  ]
}
```

## Execution semantics

- Dependencies are executable AND prerequisites. A node is runnable only when
  every named dependency is mechanically proved.
- Ready nodes from different approach families are selected before a second
  node from an already represented family. This is a diversity-first ordering,
  not a fixed per-family allocation.
- Newly unlocked, never-attempted dependencies are executed automatically on
  the following research round. System 2 does not have to remember to resubmit
  them.
- Legacy midpoint and lemma-chain actions still work and are registered as
  observations without changing their execution order.
- The blackboard remains the trusted lemma store. The obligation graph records
  search state; Lean remains the final proof boundary.

## Families and lifecycle

The graph stores both an LLM-declared family and a normalized family. Known
equation shapes—projection, row/column constancy, operation collapse, square
normalization, and sandwich normalization—override superficial free-form
labels. Unknown mechanisms retain a sanitized declared family.

Node states are:

```text
proposed -> active -> proved
                   -> refuted
                   -> retryable -> blocked
blocked  -> proposed only with a new reopen_novelty mechanism
```

Proved and refuted states require mechanical evidence. Repeated budgeted
attempts without decisive progress eventually block a node. Resubmitting the
same blocked equation requires both an explicit novelty statement and a new
mechanism signature; simple alpha-renaming is already collapsed by canonical
equation signatures.

Every episode persists the graph, family registry, evidence, attempts, blocked
reasons, and reopen history. Verified proof-plan lessons distilled from the
episode retain family, mechanism, dependency, alternative-group, and target
metadata.

## Real probe

Run:

```bash
python3 scripts/obligation_graph_probe.py
```

The v1 right-square probe begins with one planner action containing:

- a square-absorption route;
- an independent left-projection adversarial alternative;
- a right-square node depending on square absorption.

The first mechanical round selected both ready families. It proved square
absorption and refuted left projection with a small model. The graph then
automatically scheduled `right_square`; the blackboard combined it with the
proved dependency, and the official Lean verifier accepted the final proof.
The family registry ended with two proved square-normalization nodes and one
refuted projection node. A capability-dropout control withholding the generic
midpoint worker failed.

## Current limits

- `alternative_group` records OR routes and supports portfolio scheduling, but
  v1 does not yet propagate proof/disproof numbers through a general AND/OR
  root-value calculation.
- Midpoint attain, consume, and audit legs still live inside the packed worker;
  they are not yet separate persistent graph nodes.
- Family inference recognizes only the first common equational mechanisms. It
  does not yet cluster representation changes or synthesized workflows.
- Block thresholds are transparent fixed parameters rather than learned
  survival estimates.
- Early-route independence is not yet enforced through context-masked proposal
  calls, and cross-family synthesis remains a planner behavior rather than a
  first-class action.

The next graph increment should promote attain/consume/audit legs to explicit
nodes and propagate root value through AND dependencies and OR alternatives.
