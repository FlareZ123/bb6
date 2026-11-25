# q32 exact queue slice and row 26

The 84-node q32 checkpoint is contained in canonical raw11, whose exact parent is `1RB---_1RC---_0LA---_------_------_------`. It covers only two normalized A1 children and cannot by itself prove the entire parent safe.

The original 34-entry roster consists of 32 side witnesses and two sweeps. The side certificates and parent refinement were Lean-accepted in [45603623804](https://github.com/FlareZ123/bb6/actions/runs/45603623804). The ten complete slice nodes plus two former partial nodes (fourteen symbolic one-hole sweeps) were accepted in [45599143180](https://github.com/FlareZ123/bb6/actions/runs/45599143180) and [45600433773](https://github.com/FlareZ123/bb6/actions/runs/45600433773), yielding `allTwelve_sound` at bound 144. 38 queue nodes remain after these closures.

## New complete candidate: queue row 26

Exact zero-based source row 26 is `1RB1RD_1RC0LC_0LA---_1LA0LB_------_------`. Local discovery produced 371 first-hole splits, 7,140 translated-cycle leaves, 1,362 last-hole leaves, 32 FAR leaves, zero unresolved, and maximum first-hole index 40 (8,905 nodes total). Bound 46 allows six additional weighted steps. Every split contains all 24 ordinary children; the established checker handles the halt sibling.

The two survivors of the width<=3 FAR bank are `1RB1RD_1RC0LC_0LA0RE_1LA0LB_0RF---_1LD1RE` and `1RB1RD_1RC0LC_0LA0RF_1LA0LB_1LD1RF_0RE---`. Both admit a non-reflected width-4 DFA with transitions [0,1,0,2,3,2,0,2], with separate saturated NFA witnesses.

[generate_q32_row26.py](generate_q32_row26.py) reuses the original parser, discovery and emitter and asserts the exact counts, row identity and absence of residuals. It generates 24 first-child proof shards and aggregate safe26. [Q32Row26Consumer.lean](Q32Row26Consumer.lean) targets exact row encoding, parent refinement, bound lift and exact complement consumption with any preceding roster.

**Acceptance:** complete computational candidate, not yet a Lean-certified theorem. Local Lean 4.36.0-rc2 reconstructed successfully; local GitHub checkout fails DNS, so the exact imported source closure requires focused CI. After acceptance, 37 untouched queue nodes and the larger parent complement remain. No global BB(6) upper bound is claimed.
