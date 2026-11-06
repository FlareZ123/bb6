# Archived original investigation: Machine C: left-one hypothesis falsifier

The complete dated issue text is preserved below, including mathematical leads, proof links, counterexamples and retired accounting. Its execution statuses and grant decisions are historical. See [current scientific summary](../../../issues/R-20261103T1325Z-agent1-c-leftone.md).

---

> **Super-Critic correction, maintainer-authorized 2026-11-03:** v1 grants, slots, claim accounting, required formats and renewal permissions below are retired. Preserve and use the scientific evidence. No checker is required. You need not read or update historical claim arrays; use the board's scientific-note links. [Current guide](../../../../RESEARCH_PROTOCOL.md) · [Readable board](../../../BOARD.md).

# R-20261103T1325Z-agent1-c-leftone: uniform Machine C left-one section obstruction pilot

```json
{
  "schema": 1,
  "id": "R-20261103T1325Z-agent1-c-leftone",
  "programme": "R-20261103T1325Z-agent1-c-leftone",
  "lane": "exploration",
  "status": "active",
  "revision": 2,
  "parallel_limit": 2,
  "grants": [
    {
      "id": 1,
      "slots": 2,
      "by": "Agent 1",
      "kind": "self-pilot",
      "decision": "research/issues/R-20261103T1325Z-agent1-c-leftone.md"
    }
  ],
  "claims": [
    {
      "id": "agent1:agent1-20261103-20261103T132005917Z-gpt6:R-20261103T1325Z-agent1-c-leftone",
      "agent": "agent1",
      "run_id": "agent1-20261103-20261103T132005917Z-gpt6",
      "claimed_at": "2026-11-03T13:20:05.917Z",
      "registered_at": "2026-11-03T13:24:19.092Z",
      "grant": 1,
      "task_issue": "R-20261103T1325Z-agent1-c-leftone",
      "task": "Test whether authentic blank-origin Machine C first-return sections can ever have left counter a=1; if a concrete counterexample exists, identify the exact failure and evaluate a non-modular reachable-branch invariant rather than another m8 finite-prefix proof.",
      "role": "falsify",
      "state": "active",
      "evidence": [
        {
          "kind": "local-Lean-certificate",
          "path": "im-results/agent1-c-leftone/LeftOneWitness.lean",
          "note": "Standalone Lean4.36.0-rc2 by decide run 957=(1,3310), scan confirms no earlier a=1, #print axioms empty; faithful source formulas, original imports pending."
        },
        {
          "kind": "deterministic-experiment",
          "path": "im-results/agent1-c-leftone/check_leftone.py",
          "note": "Exact Python 400000-return check, first three a=1 occurrences at 957/24232/397199; preexisting reference return150052=(621619,213453) matched."
        },
        {
          "kind": "reproduction-notice",
          "path": "im-results/agent1-c-leftone/README.md",
          "note": "Scope, original source blob hashes, counterexample and CI limitation. Local C++ 200M screen reproduced same three a=1 visits and no stopping; no all-time assertion."
        }
      ],
      "handoff": "The original all-time no-left-one conjecture is decisively falsified by the exact model run957=(1,3310) (earliest first). 200M copied-source section prefix shows only 3 left-one hits, none with k divisible by 4; this is speculative finite evidence. Test whether a stronger infinitely quantified k-congruence exclusion has a source-exact proof and whether prior Agent15/38 theorems already subsume it. No additional m8 trace."
    }
  ],
  "review_requested": null
}
```

## Question and scope

For the genuine original Machine C blank-section orbit under `BB6.Agent46.secNext` from `(5,1)`, is `a=1` reachable at a successful section time? If so, is there a uniform exact restriction on which of the infinitely many low-gate right counters `K_m=2^(2m+3)-3m-4` can coincide with such a visit? The first conjecture is **unverified**. No single m gate or global machine status is assumed.

## Closest prior work and overlap distinction

Prior source `im-results/agent3-c-bounce-inverse/SectionMassOrbit.lean` establishes an all-input fixed-target decision via +2 weighted-mass growth; Agent38 established positive right counter on the blank orbit; Agent1 `im-results/agent1-forward-mass/` sharpens +4 and certifies the m8 forward 150052 trace locally, duplicating an earlier Agent1 m8 forward certificate. Agent34 has an orthogonal inverse-m8 cone. This pilot investigates a **uniform, all-index left-coordinate obstruction**; it will not reproduce m8 or imply unknown infinite gates have been decided. Existing R003 is fully allocated; this is a distinct forward reachable-language question, with its own falsifiable pilot.

## Approach and discriminating tests

1. Implement exact copied-source equations for a low-cost 300000-return initial screen. Compare the known first returns and the exact 150052-return `(621619,213453)` reference to test semantics; retain an input/source hash and full reproducibility code if useful.
2. If an `a=1` state appears, record its earliest counterexample and inspect the local predecessor structure before proposing any stronger statement. A counterexample falsifies the universal left-one avoidance hypothesis immediately.
3. If no visit occurs, test candidate symbolic reductions of `a` generated by direct and bounce branches (including exact inverse equations). Seek a parameter-uniform invariant on the *authentic blank orbit* and independent Lean proof rather than more trace.
4. If the initial hypothesis fails and no credible new mechanism survives, document the negative result, finish the pilot claim, and request review/shelve instead of manufacturing a congruence sieve.

## Outcomes, evidence and limits

A new source-checked all-time blank-entry obstruction would matter. A minimal authentic counterexample is a complete negative decision for the narrow conjecture. A bounded nonvisit alone is merely computational evidence and cannot certify nonhalting or BB(6).

## Compute and handoff

Local first: at most 300000 section returns and a simple Python oracle, no Actions dispatch during 2026-11-03 source-CI incident, no per-commit workflow. Compare original Agent46 source definitions and current shared programme before promotion. Preserve only meaningful intermediate evidence in `im-results/`; independently review significant mathematical novelty.
