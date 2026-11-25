# q32 exact queue-slice certificates

The 84-node q32 checkpoint is contained in canonical raw11, whose exact parent is `1RB---_1RC---_0LA---_------_------_------`. It covers only two normalized A1 children; it is not a complete cover of raw11.

## Accepted closure

The original 34-entry roster consists of 32 side witnesses and two sweeps. The side certificates and parent refinement were Lean-accepted in [45603623804](https://github.com/FlareZ123/bb6/actions/runs/45603623804). The ten complete slice nodes plus two former partial nodes (fourteen symbolic one-hole sweeps) were accepted in [45599143180](https://github.com/FlareZ123/bb6/actions/runs/45599143180) and [45600433773](https://github.com/FlareZ123/bb6/actions/runs/45600433773), yielding `allTwelve_sound` at bound 144.

**Exact zero-based source row 26** is `1RB1RD_1RC0LC_0LA---_1LA0LB_------_------`. Its complete source tree was accepted by the "Certify q32 row 26 from exact source tree" step of [45679145466](https://github.com/FlareZ123/bb6/actions/runs/45679145466), including the axiom guard: `safe26` proves weighted bound 46 for every compatible completion. There are 371 first-hole splits, 7,140 translated-cycle leaves, 1,362 last-hole leaves, 32 FAR leaves, zero unresolved, and maximum first-hole index 40 (8,905 nodes). Two survivors of the width<=3 bank share the width-four non-reflected DFA [0,1,0,2,3,2,0,2]. The subsequent parent-consumer step failed due to unrelated RootRaw10Core.lean syntax; that is not a failure of the accepted row theorem.

[generate_q32_row26.py](generate_q32_row26.py) rebuilds the exact audited row and 24 proof shards. [Q32Row26Consumer.lean](Q32Row26Consumer.lean) states its parent refinement and conditional exact-complement consumption; the latter requires its own source check.

## New row 34

[Q32Row34.md](Q32Row34.md) describes the complete candidate at bound 129, including the common all-length block-stack invariant for the two final symbolic leaves. Macro proofs and arbitrary live prefixes were checked in the exact extracted local sweep semantics; original source and full audit CI [45680263374](https://github.com/FlareZ123/bb6/actions/runs/45680263374) are pending.

37 queue nodes remain beyond the original 34, the accepted 12, and row 26; if row 34 passes, 36 remain. The larger raw11 parent complement must still be closed separately.
