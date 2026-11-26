# q0 active root 52 — exhaustive candidate at weighted bound 4,663

**Mathematical status:** the complete candidate tree has no unresolved leaf; original-source Rocq acceptance and the packed checkpoint consumer are still required. This is an intermediate proof-search result, not a global roster subtraction.

Root 52 of the pinned q0 active export is `1RB1RD_1RC1LE_0LA---_1LA1LD_------_------` (five holes). An exhaustive first-undefined-transition tree uses all 24 ordinary transitions at every split, with no fresh-state quotient. The source contract includes the halt branch with its incoming delay allowance of six.

| Node type | Count |
|---|---:|
| Translated cycles | 17,963 |
| Coarse two-DFA closures | 3,381 |
| First-hole splits | 1,142 |
| Last-hole trace leaves | 4,912 |
| Additional finite automata | 11 |
| Total | 27,409 |

The initial 1,500-step budget leaves twelve tables. Eleven have forward FAR/reverse-subset certificates, with 2,025 explicit primitive closure rows in the original orientation. Completing missing push edges by a sink and rerunning the dynamic two-stack MITM checker succeeds on all eleven. The twelfth is a **halting partial table** `1RB1RD_1RC1LE_0LA0RC_1LA1LD_---0LF_1LB0LB`: exact direct replay reaches E0 after 4,657 ordinary transitions. Since it is the sole undefined slot, any halting completion must halt there; an ordinary continuation has no remaining undefined slot. The candidate bound is thus 4,663 in the existing weighted source convention, not 107 from the initial short traces.

The complete generation was tested locally with equivalent transcriptions of the repository classifiers; the checked-in generator reuses the repository implementations and rejects any unexpected total, missing certificate, or long-halt mismatch. It emits 24 first-level dependency shards, with individual reflected tree checks of at most 400 nodes, and composes the cuts using `source_first_hole_split`. A missing branch cannot disappear through the assembly: the proof explicitly destructs every ordinary move. The existing packed-checkpoint consumer retains all other active and held nodes.

Reproduce from this directory: `node q0-root52.cjs 52 /tmp/Agent5Q0AutoData.v`. The existing manual `enumerate62-q0-auto-root` target with offset 52 generates the exact source against the pinned BusyCoq revision. The cut proofs are source drafts pending actual acceptance; local Coq is unavailable and local git DNS failed. Lean 4.36.0-rc2 was reconstructed successfully but does not itself verify Rocq source. No new accepted q0 root count is claimed.
