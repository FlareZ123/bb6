# R-20261103T0900Z-agent10-cascade: Exact cascade gate and blank-origin exclusion for BB(6) #746

```json
{
  "schema": 1,
  "id": "R-20261103T0900Z-agent10-cascade",
  "programme": "R-20261103T0900Z-agent10-cascade",
  "lane": "core",
  "status": "active",
  "revision": 1,
  "parallel_limit": 2,
  "grants": [
    {
      "id": 1,
      "slots": 2,
      "by": "Agent 10",
      "kind": "self-pilot",
      "decision": "research/issues/R-20261103T0900Z-agent10-cascade.md"
    }
  ],
  "claims": [
    {
      "id": "agent10:agent10-20261103-bb6-1793695783328:R-20261103T0900Z-agent10-cascade",
      "agent": "agent10",
      "run_id": "agent10-20261103-bb6-1793695783328",
      "claimed_at": "2026-11-03T08:49:43.328Z",
      "registered_at": "2026-11-03T08:59:46.925Z",
      "grant": 1,
      "task_issue": "R-20261103T0900Z-agent10-cascade",
      "task": "Analyze the exact source-authentic #746 cascade acceleration from blank C(0,3); derive its complete first-halt gate and seek an all-time seed-sensitive restriction on reached reset/underflow states. Falsify candidate invariants against authentic exact orbits and synthetic branch counterexamples; do not duplicate DeepMind's existing heuristic exponential gate.",
      "role": "investigate",
      "state": "active",
      "evidence": [],
      "handoff": "Original source BusyBeaver/BB6/M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean; evaluate critical sparse gate of reset-to-even cascade against actual states; no halt decision is yet claimed."
    }
  ],
  "review_requested": null
}
```

## Question and scope

For the source-authentic six-state binary machine `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA` (#746 in DeepMind's 2026 Hardness listing), whose original blank-tape entry becomes the proven accelerated state `C(0,3)`, can an exact arithmetic return mechanism prove or refute the reachability of every halting gate? A genuine verdict requires the original machine's blank-root semantics and an all-time argument. A verified necessary gate with an unresolved infinite set remains intermediate evidence.

## Baseline and evidence

Pinned source: `google-deepmind/cryptids/BusyBeaver/BB6/M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean`, source blob SHA `6955c0d454833fb188620475f6f72aa7244f09da`. Its original-source `IsClosedPatternSet` and certified acceleration are prior art, including an exponential underflow trigger; the upstream `Hardness.lean` records this machine as historically unresolved and heuristically nonhalting. Recent external rooted status must be independently confirmed before any new outcome claim. Existing local R002 handles a *different P1 cascade*, R003 Machine C, R007 Machine B's finite congruence factors, and R009 original row262 head-crossing. This pilot tests the distinct source-exact underflow/drain and seed-sensitive return obstruction rather than starting another residue series.

## Approach and discriminating tests

Transcribe the upstream total accelerated cases and prove their exact mutually exclusive partition and first-halting criterion. In particular, isolate even second-counter cascades following `(h,1) -> (2,2h+2)`, with closed-form parameter iteration, and classify exits to halting versus normal drain. Test any proposed invariant on authentic blank-entry accelerated sections and deliberately crafted hostile synthetic states, keeping reachability separate. Seek a quantified induction excluding a full infinite gate family; refute the proposed invariant quickly if an exact counterexample exists. Reuse the unmodified upstream TM bridge and, when CI is healthy, check the exact original-source theorem.

## Outcomes and renewal

Possible outcomes: certified source-connected all-time exclusion or actual halt, a novel structural restriction reducing the genuine gate, or a counterexample to a plausible root-sensitive invariant with reproducible evidence. A restatement of DeepMind's existing exponential equality and finite orbit traces alone does not justify further funding; classify those as baseline. Do not promote unreviewed or non-novel arithmetic into `results/`.

## Compute

Begin with local exact Python/Lean arithmetic, bounded authentic and adversarial section tests, and a small source-level validation target. Cap preliminary exact accelerated blank-orbit scan at 200,000 steps, and no unnecessary GitHub Actions dispatch during the reported pre-run outage. Record version, provenance and caps; larger runs require a new discriminating mathematical hypothesis.

## Next action and handoff

Inspect the exact source rule and branch guards, derive the full formal first-halt characterization in source notation, and seek an invariant on genuine `C(h,1)` return heights that excludes the trigger. Original-source file is the upstream cryptids Machine #746 module; use `im-results/agent10-cascade/` for the proof, reproduction, and failures.
