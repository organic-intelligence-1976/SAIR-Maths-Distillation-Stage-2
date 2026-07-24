# Structural Verified-Lesson Retrieval v1

Status: working vertical slice, 2026-07-20

The research runtime can now turn an accepted proof episode into a typed,
structurally triggered lesson and retrieve it for a related problem without
using problem IDs or transcript similarity.

## Stored lesson

A `proof_plan_schema` artifact now contains:

- canonical hypothesis/goal structure;
- the capability mask under which the lesson was produced;
- mechanically proved plan nodes and their canonical signatures;
- predecessors that were available when each node was proved;
- compact failure signals observed before success;
- a replayable action template;
- the original episode and final Lean verification as evidence.

The trigger is invariant to variable renaming and equality orientation. It also
records the opposite-magma fingerprint. When a query is the magma dual of a
source, retrieval explicitly transforms every helper equation into its dual
before replay; it does not blindly reuse the original equations.

## Retrieval

`ExperienceStore.retrieve_artifacts` scores verified artifacts using:

- exact alpha/orientation-invariant problem structure;
- explicit magma duality;
- exact or coarse hypothesis and goal shapes;
- transparent structural-feature overlap;
- capability-mask agreement;
- overlap with the target's mechanically verified partial plan.

Every result carries `_retrieval` metadata containing the score, reasons,
matched nodes, missing nodes, and any required plan transformation. Semantic
class is a small bonus for structural queries, not a hard boundary. Problem IDs
and raw transcript text are never scoring inputs.

`RetrievedLessonPlanner` is the deterministic test consumer. It submits only
the missing nodes from the best verified lesson. The target mechanical worker
must prove those equations again, and the final proof must pass the official
Lean verifier. Thus retrieval changes proposal quality but not the soundness
boundary.

## Load-bearing transfer probe

Run:

```bash
python3 scripts/structural_retrieval_probe.py
```

The v1 probe performs five checks:

1. solve the original right-square curriculum and distill its verified lesson;
2. mechanically establish only `square_absorb` on a predeclared alpha-renamed,
   equality-reversed target;
3. show that the same partial target is exhausted when retrieval is disabled;
4. retrieve the source lesson, select only the missing `right_square` node,
   mechanically reprove it on the target, and obtain an accepted Lean proof;
5. show that a structurally unrelated target retrieves no lesson.

The first run passed all five checks. The positive match scored `120.0` with
the reasons `exact_alpha_and_orientation_invariant_pair`,
`same_semantic_class`, `same_capability_mask`, and
`verified_partial_plan_overlap:0.500`. Retrieval selected one missing node; the
blackboard retained the already proved node. The no-retrieval control ended
`planner_exhausted`, while the retrieval treatment was accepted.

## Limits and next generalization

- The verified transfer probe covers one structural family.
- The consumer is deterministic; a live LLM has not yet been measured on the
  same blinded retrieval contract.
- Fingerprints and scores are transparent hand-built features, not a learned
  similarity model.
- `predecessors_available` does not claim logical necessity. True alternatives
  and dependencies still require a first-class lemma obligation DAG.
- V1 transports known helpers. It has not yet demonstrated a helper schema
  absent verbatim from every retrieved lesson.

The next architectural step is to represent retrieved and newly proposed nodes
in one persistent AND/OR lemma DAG. The next curriculum step is to repeat this
probe across dual, disguised, multi-family, and absent-verbatim-schema tasks.
