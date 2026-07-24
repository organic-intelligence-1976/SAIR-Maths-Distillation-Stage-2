# True-Side Midpoint Roadmap

## Current Diagnosis

The highest-value true-side failures are often not caused by a missing theorem
search core. The solver already derives useful universal midpoint lemmas in many
cases, but the renderer cannot always use them to finish the original goal.

Recent examples:

- `hard3_0187`: derived `forall a b c, a * b = a * c`; solved after adding a
  one-step `h` plus midpoint `calc` stitch.
- `hard2_0198`: same row-constancy shape; solved by the same stitch.
- `hard3_0183`: derives a useful row-idempotent form, but needs repeated use of
  that midpoint toward a common reduct.
- `hard3_0266` and `hard3_0314`: projection-style midpoint cases. `hard3_0266`
  now solves after a tightly bounded variable-overlap superposition pass derives
  right projection; `hard3_0314` still needs a richer projection proof search.

## Priority 1: Repeated Midpoint Stitching

Build a small equality-path renderer after a midpoint is proved.

Inputs:

- original hypothesis `h`;
- proved universal midpoint `target`;
- goal lhs/rhs.

Search:

- generate terms from goal subterms plus terms reached by one `h` instantiation;
- add equality edges from direct `h` instantiations;
- add equality edges from direct midpoint instantiations;
- find a short path from goal lhs to goal rhs;
- render the path as a Lean `calc`.

This keeps the same soundness story: every edge is a concrete Lean expression,
and the final proof is kernel-checked.

Expected wins:

- repeated rowconst/idempotent cases such as `hard3_0183`;
- projection cases where several local rewrites are needed.

### Experiment: Small Equality-Path Stitcher

Implemented a bounded equality-path stitcher in `render_pc`:

- direct universal midpoint matching with orientation handling;
- one `h` step plus one midpoint application;
- repeated short paths over concrete `h` and `target` instantiations.

New deterministic wins with LLM disabled:

| Case | Before | After |
|------|--------|-------|
| `hard2_0198` | unsolved, LLM fallback | solved in about 9s |
| `hard3_0187` | unsolved, LLM fallback | solved in about 8-9s |
| `hard3_0183` | unsolved, LLM fallback | solved in about 8s |

Still not solved by this experiment:

- `hard2_0107`
- `hard3_0314`

Interpretation:

- repeated direct use of rowconst/idempotent-style midpoints is now useful;
- projection-style cases likely need contextual rewriting under larger terms or
  a richer term pool/path search;
- recursive midpoint proving remains lower priority until this stitcher can
  consume proved lemmas in more contexts.

### Experiment: Variable-Overlap Projection Lemmas

Implemented an opt-in proof-carrying superposition pass that allows
paramodulation into variable positions. This is not part of the default
goal-direct search because it can expand quickly; it is only tried for auxiliary
lemmas already predicted by the counterexample filter, with strict caps.

Also changed the equality-path stitcher to try proved midpoint/target rewrites
before raw `h` rewrites. This prevents simple projection paths from being crowded
out by larger `h` expansions.

New deterministic win with LLM disabled:

| Case | Before | After |
|------|--------|-------|
| `hard3_0266` | unsolved, projection implied but not proved | solved in about 16-17s |

Remaining projection miss:

- `hard3_0314`: right projection is semantically implied, but the cheap
  variable-overlap bounds do not derive it. A broader pass was too expensive for
  default use, so the next experiment should either target the E-style proof
  shape more directly or add a more disciplined completion/rewrite simplifier.

### Experiment: CE-Guided Solve-Order Triage

Moved proof-carrying auxiliary-lemma superposition ahead of the broad
HAVE+GRIND battery when `h` has free variables and the counterexample filter
predicts a standard helper lemma. The old later goal-direct superposition remains
as a fallback, but aux lemmas already tried early are not repeated later.

This is a runtime/triage improvement, not a new trusted proof mechanism: every
candidate body is still checked by Lean.

Observed LLM-disabled improvements:

| Case | Before | After |
|------|--------|-------|
| `hard3_0183` | ~8.4s, 11 judge calls | ~3.3s, 1 judge call |
| `hard3_0187` | ~7.3s, 11 judge calls | ~2.2s, 1 judge call |
| `hard3_0266` | ~16-17s, 11 judge calls | ~7-8s, 1 judge call |
| `hard2_0198` | ~9.0s, 11 judge calls | ~3.3s, 1 judge call |

The original 10-case true smoke still solved 10/10 after the ordering change,
with most cases closing in one judge call.

### Experiment: Type-Sensitive Early-Aux Caps

The next slow solved case, `hard1_0034`, looked at first like an expensive
counterexample-search problem. Direct timing showed the full CE search was cheap;
the real delay was the CE-guided early auxiliary proof route trying an implied
`rowconst` lemma for its full mini-budget, producing no body, and only then
falling back to the ordinary battery proof.

Changed the early auxiliary budget by helper type:

- projection helpers (`proj_l`, `proj_r`) get a longer cap because the
  variable-overlap projection proof can need several seconds;
- `const` gets a medium cap;
- `rowconst` gets only a short scout cap, because if it is not found quickly the
  battery should get control.

Observed LLM-disabled result:

| Case | Before | After |
|------|--------|-------|
| `hard1_0034` | ~19-20s, 4 judge calls | ~7-8s, 4 judge calls |

Regression after the cap:

- the 10-case true smoke still solved 10/10;
- `hard3_0183`, `hard3_0187`, `hard3_0266`, and `hard2_0198` remained one-judge-call solves.

## Priority 2: Better LLM Midpoint Interface

Once the stitcher can use a midpoint repeatedly, improve what the LLM can provide.

Recommended next LLM experiment:

- use the LLM only as an untrusted universal-lemma proposer;
- ask for a ranked list of 5-10 candidate midpoint equations;
- mechanically test each candidate with the existing `midpoint_stitched_bodies`
  route;
- accept only candidates where Lean checks both legs.

Useful outputs:

- one midpoint equation;
- a ranked list of candidate midpoint equations;
- optional suggested terms/instantiations for using the midpoint.

Good candidate shapes to ask for:

- standard helpers: `a = b`, `a ◇ b = a`, `a ◇ b = b`,
  `a ◇ b = a ◇ c`;
- idempotence and absorption: `a ◇ a = a`, `(a ◇ b) ◇ b = b`,
  `a ◇ (a ◇ b) = a ◇ b`;
- bridge equations between visible goal subterms;
- one-step simplifiers that reduce either side of the goal toward a shared
  reduct.

Prompting notes:

- show the hypothesis, goal, known goal subterms, and any standard helper lemmas
  that the CE filter could not refute;
- ask for JSON only, e.g.
  `{"verdict":"midpoints","lemmas":["a ◇ b = b", "..."]}`;
- emphasize that the LLM output is a hint, not a proof, and will be discarded if
  the mechanical prover cannot close it.

Ranking notes:

- first rank by cheap syntactic features: size, variables used, overlap with
  goal subterms, and whether the lemma is a standard helper;
- prefer lemmas whose lhs/rhs can match a visible goal subterm under substitution;
- penalize very large lemmas, lemmas with many variables, and lemmas containing
  fresh structure absent from both hypothesis and goal.

Frontier cases worth trying first:

- `hard2_0107`: current system derives a useful-looking target but does not
  close the goal;
- `hard3_0314`: right projection is semantically implied, but current bounded
  projection proof search does not derive it cheaply.

Current limitation:

- the production solver treats multiple LLM midpoint strings as alternatives,
  not a chain;
- the sidecar now has one narrow `lemma_chain` consumer for the
  square-witness family, but this has not been generalized to arbitrary
  multi-rung proof trees.

Implementation sketch:

```text
for M in LLM_midpoint_candidates(H, G):
    if mechanical(H, M) and mechanical({H, M}, G):
        return stitched_proof(M)
return unsolved_or_next_route
```

Non-goals for the first LLM experiment:

- do not ask the LLM to write Lean proof bodies;
- do not share full Lean proof attempts unless midpoint-only hints stop paying;
- do not implement recursive multi-midpoint chains until single-midpoint
  consumption is measured on the frontier.

### Experiment: Square-Witness Lemma Chain

Added `lemma_chain` mode to the sidecar for the hand-proof shape behind
`hard1_0018`.

The LLM supplies the untrusted chain:

- `u ◇ u = v ◇ v`
- `u ◇ (v ◇ v) = u`
- `(v ◇ u) ◇ v = u`
- `v ◇ (u ◇ v) = u` when the stuck term has the dual sandwich shape

The sidecar proves the helpers explicitly, then runs a tiny verified simplifier
using only those helpers. The fourth helper is derivable from the first three
plus one more H-instantiation, so the renderer can also close older three-lemma
chain replays. This is a chain consumer, not a trusted proof: every helper and
the final goal proof are checked by the judge.

Observed result:

| Case | Result |
|------|--------|
| `hard1_0018` | solved by replayed chain and by live `gpt-oss-120b` in round 0 |
| `hard3_0231` | solved after adding the derived `left_sandwich` rule; live `gpt-oss-120b` returns the four-lemma chain in round 0 |

Interpretation:

- this is the first clear case where the LLM helps by naming a multi-rung
  mathematical plan rather than a single midpoint;
- precise normal-form feedback was enough to identify the next derived helper
  for the related `hard3_0231` shape;
- the useful next generalization is not full recursion yet, but a small library
  of verified simplifier rules plus precise normal-form feedback.

## Priority 3: Share More Proof Context With The LLM

The proxy currently includes judge statuses and truncated Lean errors in
`history.attempts`, but not the full generated Lean code for failed attempts.

Potential later improvement:

- summarize failed mechanical proof attempts and derived lemmas in
  `solver.analysis`;
- include the last generated candidate body or distilled lemma list when useful.

This is lower priority until the deterministic stitcher can exploit good hints.

## Priority 4: Recursive Midpoint Proving

Recursive midpoint proving is valuable, but only after midpoint consumption is
strong enough.

Target architecture:

```text
prove(H, G):
  if mechanical(H, G): return proof
  M = untrusted midpoint hint
  pM = prove(H, M)
  pG = prove({H, M}, G)
  stitch pM and pG
```

Current reason to defer:

- several unsolved cases already have mechanically derivable midpoints;
- the main bottleneck is using one proved midpoint many times, not proving the
  midpoint recursively.
