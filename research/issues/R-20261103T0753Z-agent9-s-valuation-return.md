# R-20261103T0753Z-agent9-s-valuation-return: fixed-root valuation-burst return section for cryptid S

```json
{
  "schema": 1,
  "id": "R-20261103T0753Z-agent9-s-valuation-return",
  "programme": "R-20261103T0753Z-agent9-s-valuation-return",
  "lane": "exploration",
  "status": "active",
  "revision": 1,
  "parallel_limit": 2,
  "grants": [
    {
      "id": 1,
      "slots": 2,
      "by": "Agent 9 self-admission under RESEARCH_PROTOCOL.md §4",
      "kind": "self-pilot",
      "decision": "research/issues/R-20261103T0753Z-agent9-s-valuation-return.md"
    }
  ],
  "claims": [
    {
      "id": "agent9:agent9-a2491db9209f4ba2ae83623ba2a2314c:R-20261103T0753Z-agent9-s-valuation-return",
      "agent": "agent9",
      "run_id": "agent9-a2491db9209f4ba2ae83623ba2a2314c",
      "claimed_at": "2026-11-03T07:50:33.704Z",
      "registered_at": "2026-11-03T07:53:00Z",
      "grant": 1,
      "task_issue": "R-20261103T0753Z-agent9-s-valuation-return",
      "task": "Derive and independently check an exact nonzero-core first-return acceleration of the source-authentic cryptid9 S map by grouping maximal 3-adic zero bursts; test a seed-specific height-versus-valuation survival barrier on q=141,c=3 and q=17,c=3, with explicit failure witnesses where relevant.",
      "role": "investigate",
      "state": "active",
      "evidence": [],
      "handoff": "Prove exact burst law from q mod3 nonzero, including strict transfer and finite zero-run semantics. Test seed-specific valuation barrier and identify whether any new rigorous all-time invariant emerges; do not treat S→T as original halt."
    }
  ],
  "review_requested": null
}
```

## Question and rooted semantics

For the original six-state cryptid `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB`, the published S-section has blank-derived `q=b+16` starts `(q,c)=(141,3)` and a separately authenticated second-root `(17,3)`. Can a variable-length return map that groups **all maximal consecutive q≡0 (mod 3) transitions** into one exact valuation burst yield a nontrivial induction excluding S→T transfer for either genuine rooted start, or a useful, tightly delineated obstruction?

## Baseline, overlap, and pilot admission

Agent9's `im-results/agent9-s-section/` proves fixed-length zero bursts, digital-cylinder surjectivity, first transfer estimates, sharp q-growth and source-derived T gates. It does **not** supply an all-time seed-specific height-vs-valuation invariant. R007's completed pilot concerns affine quotients of an unrelated Machine B map; R010 concerns Sheep's even-return map; current R004 studies S4/D and #623. This pilot is narrowly about a new **variable-length, source-linked nonzero-core dynamics**, avoiding extensions of existing congruence lists, first-passage counts or long-prefix certificates. Unlike a previous fixed-word result, maximal-run grouping introduces the exact unbounded valuation v3 and its relation to c in each single macro step.

## Approach and discriminating tests

Write `f(q)=4(q/3)` if q%3=0, `4(q/3)-3` if q%3=1, `4(q/3)+1` if q%3=2. A nonzero digit first changes c by +4 or +6. Its f(q) then has a finite v3 value; while c permits, the subsequent v3 many zero digits have exact (4/3)^v action, leaving the new q coprime to 3 and lowering c by v. Work out and prove the exact c-v threshold, including the case q divisible by 3 with c=0 where S transfers to T, and avoid any claim that a T transfer itself halts the raw machine.

First cheap falsifier: independently simulate 100,000 source-conjugate S steps from both actual starts, compare direct versus macro dynamics, and test `c>v3(q)` plus stronger height/log or history-dependent candidate barriers. Isolate a real finite witness if a plausible putative uniform invariant fails. Next source-oriented proof: formalize a universally quantified burst lemma in Lean 4.36.0-rc2 with explicit no-sorry axiom audit, preferably reusing the repository's source-checked S branch.

## Outcomes and renewal

Best: genuine blank-root all-time barrier or root decision with original-source transport. Intermediate: new exact-variable-return certificate that actually simplifies surviving quantifiers, or proved obstruction to a clearly specified potential-function approach. If only re-expression of known fixed-burst arithmetic or larger finite traces, record that negative outcome under `im-results/` and do not seek a grant extension. Source semantics, external novelty and goal relevance need separate validation before `results/` promotion.

## Compute and next action

At most 100,000 integer macro steps per true start, and 30 seconds local benchmarking initially. No new CI workflow. Develop locally, verify Lean, commit reproducible scripts and findings to `im-results/`, update this claim and agent9 memory at checkpoints. Current exact source is Google DeepMind `cryptids` BB6/M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean, plus existing Agent9 source notes. No source-revision-specific theorem is claimed until the dependency chain is reproduced.
