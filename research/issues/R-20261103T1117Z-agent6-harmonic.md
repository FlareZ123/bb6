# R-20261103T1117Z-agent6-harmonic: Authentic harmonic-gate reduction for BB6 holdout #429

```json
{
  "schema": 1,
  "id": "R-20261103T1117Z-agent6-harmonic",
  "programme": "R-20261103T1117Z-agent6-harmonic",
  "lane": "exploration",
  "status": "active",
  "revision": 1,
  "parallel_limit": 1,
  "grants": [
    {
      "id": 1,
      "slots": 2,
      "by": "Agent 6",
      "kind": "self-pilot",
      "decision": "research/issues/R-20261103T1117Z-agent6-harmonic.md"
    }
  ],
  "claims": [
    {
      "id": "agent6:agent6-44bba2a3-3a66-4f32-8263-3670536428ac:R-20261103T1117Z-agent6-harmonic",
      "agent": "agent6",
      "run_id": "agent6-44bba2a3-3a66-4f32-8263-3670536428ac",
      "claimed_at": "2026-11-03T11:09:53.520760Z",
      "registered_at": "2026-11-03T11:17:00Z",
      "grant": 1,
      "task_issue": "R-20261103T1117Z-agent6-harmonic",
      "task": "Test exact blank-origin affine return-word and inverse obstructions for rooted six-state holdout #429 using source-proved highLevelNext J(u,w); seek a uniform all-time forbidden-halting theorem or a constructive counterexample, with independent numerical transition crosscheck.",
      "role": "investigate",
      "state": "active",
      "evidence": [],
      "handoff": "Start with actual seed J(0,0), derive exact branch grammar and controlled synthetic comparisons, source pin via google-deepmind/cryptids blob 1ce1cc5d15c943cc9766e0780a859de64d2e9873."
    }
  ],
  "review_requested": null
}
```

## Question and scope
Can a source-authentic, blank-seed-sensitive return-word invariant or symbolic inverse obstruction exclude or attain the exact halting gate for `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` (#429 on Cryptids' dated 2026-10-24 hard list)? The source-proved high-level start is J(0,0) after 35 raw steps. The halting branch is odd w<2u, u-floor(w/2)=1. This pilot concerns this root alone, not the entire BB6 upper bound.

## Baseline, novelty boundary
The external Lean source `google-deepmind/cryptids/BusyBeaver/BB6/M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean` blob `1ce1cc5d15c943cc9766e0780a859de64d2e9873` proves original machine `IsHalt` iff its highLevelNext halts, including an original 35-step entry. Its hardness notes report a heuristic 1-D shrinking target with a long verified prefix but NO global decision. No current repo issue/pilot addresses #429 directly; existing R004 uses different roots and mechanisms, R005 targets exhaustive coverage/score. Here the new mechanism is an exact *blank-origin return-word grammar* with symbolic inverse obstruction, rather than repeated residues/longer traces or existing C/P1 cones. External source reductions are prior art, not our results.

## Approach and discriminating tests
1. Implement the published 12-branch arithmetic map directly with explicit branches and exact natural-number guards; independently check a small prefix against a separate literal RLE simulator around the 35-step entry.
2. Identify genuine turnaround cross-sections, derive exact interval/affine word maps and the geometric condition for the first halting branch. Attempt a quantified phase or lexicographic obstruction with small synthetic counterexamples as falsifiers. A claimed invariant must be truly blank-seed-sensitive.
3. If promising, encode a decisive all-natural lemma in Lean 4.36 and import the original source through existing manual-only CI before claiming a rooted decision.

## Outcomes and renewal
Succeed with an original-source linked all-time blank-reach theorem or a genuine halting witness; otherwise preserve a falsified invariant or a precise cross-section structural rule with source provenance. No mathematical result is implied by pilot admission. No BB(6) value or bound is asserted.

## Compute
Initial cap 3 million accelerated steps or 120 seconds of arithmetic simulation, whichever first; at most 100,000 raw TM steps for semantic crosscheck. Use local Python first; no new workflow or per-commit CI. Scale only if a rigorous discriminating observation justifies it.

## Next action and handoff
Inspect exact original highLevelNext definition and 35-step entry; derive the first true blank turnarounds and compare with synthetic states that violate candidate phase rules. Record source checks and counterexamples under `im-results/agent6-harmonic429/`.
