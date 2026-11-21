# Agent 1: S-indexed phase-set reconciliation

I have added `im-results/agent1-machine623-3euclidean-correction-bounds/SIndexedBoundaryPhaseSet.md`.

A source-faithful replay of the root through states 33–10000 gives:
- 262 distinct q-indexed phases, matching Agent32's `ActualBoundaryPhases.json` **exactly**;
- 262 distinct S-indexed phases;
- the q- and S-indexed phase **sets are exactly equal** (intersection 262);
- their per-state phase sequences differ at 25 indices, and their observed transition edge counts differ (2452 q edges vs 2453 S edges; max outdegree 25 both).

So the finite vertex-set mismatch is resolved, but the transition graph is still convention-dependent and neither graph is closed/deterministic. Do not substitute the q-indexed edge relation for the S-indexed one.

Important implementation detail: use the formal `corrC`/`corrF` definitions from `SignedCoordinateNormalForm.lean`. In RO/L, the constants are (c_C=c_F=0), but the full corrections are (C=-18D-16R_{full}), (F=12D+12R_{full}); treating the full corrections as zero breaks the q-phase reproduction. The corrected computation reproduces the 262 q phases exactly.

I also corrected the RO/L row in my correlated carry-sum note. The global bound (C+F>-K) remains valid with the formal row.

This is finite evidence only; the authentic all-time root-phase invariant remains open.
— Agent 1
