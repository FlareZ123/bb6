# q0 active root 52 — kernel-checked weighted bound 4,663

**Mathematical status:** complete local Lean kernel acceptance of `Q0Root52.safe_root : Cover (WeightedBound 4663) Q0Root52.rootParent`, 2026-11-26. Every compatible completion is covered. The original-source Rocq proof and packed-checkpoint consumer are separate and remain pending; no global roster subtraction is asserted.

Root 52 of the pinned q0 active export is `1RB1RD_1RC1LE_0LA---_1LA1LD_------_------` (five holes). An exhaustive first-undefined-transition tree uses all 24 ordinary transitions at every split, with no fresh-state quotient. The source contract includes the halt branch with its incoming delay allowance of six.

| Node type | Count |
|---|---:|
| Translated cycles | 17,963 |
| Coarse two-DFA closures | 3,381 |
| First-hole splits | 1,142 |
| Last-hole trace leaves | 4,912 |
| Additional finite automata | 11 |
| Total | 27,409 |

The initial 1,500-step budget leaves twelve tables. Eleven have forward FAR/reverse-subset certificates, with 2,025 explicit primitive closure rows in the original orientation. Completing missing push edges by a sink and rerunning the dynamic two-stack MITM checker succeeds on all eleven. The twelfth is a **halting partial table** `1RB1RD_1RC1LE_0LA0RC_1LA1LD_---0LF_1LB0LB`: exact direct replay reaches E0 after 4,657 ordinary transitions. Since it is the sole undefined slot, any halting completion must halt there; an ordinary continuation has no remaining undefined slot. The proved Lean weighted bound is thus 4,663 in the existing weighted source convention, not 107 from the initial short traces.

The complete generation was tested locally with equivalent transcriptions of the repository classifiers; the checked-in generator reuses the repository implementations and rejects any unexpected total, missing certificate, or long-halt mismatch. It emits 24 first-level dependency shards, with individual reflected tree checks of at most 400 nodes, and composes the cuts using `source_first_hole_split`. A missing branch cannot disappear through the assembly: the proof explicitly destructs every ordinary move. The existing packed-checkpoint consumer retains all other active and held nodes.

Reproduce from this directory: `node q0-root52.cjs 52 /tmp/Agent5Q0AutoData.v`. The existing manual `enumerate62-q0-auto-root` target with offset 52 generates the exact source against the pinned BusyCoq revision. The cut proofs are source drafts pending actual acceptance; local Coq is unavailable and local git DNS failed. Lean 4.36.0-rc2 was reconstructed successfully but does not itself verify Rocq source. No original-source Rocq count is claimed.

## Accepted complete Lean proof

Reused the exact generated Rocq source witness artifact **15102359679** (run 45792833561), rather than repeating the search. The generalized translator [generate_q0_exhaustive_lean.py](generate_q0_exhaustive_lean.py) emits 24 first-level Lean shards, each with small checked subtrees of at most 49 nodes. [Q0ExhaustiveTree.lean](Q0ExhaustiveTree.lean) proves the exhaustive all-24-ordinary-moves plus immediate-halt coverage rule. [Q0Trace.lean](Q0Trace.lean) and [q0_trace_emit.py](q0_trace_emit.py) isolate the 4,657-step final-hole execution in 37 sparse zipper segments (128 steps except the last), with exact checked configurations and a proof of concatenation. The generator's output was reproduced byte-for-byte against the checked 27 files.

Local Lean 4.36.0-rc2 (b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a), imported Canonical77 artifact 14997966221 (run 45554648116), repository TwoSidedAutomata, Q0ExhaustiveTree (blob af9a88a684425b17b01d4e0538e7edac58e8b09a), Q0Trace. Every one of the 24 shard theorems and the final parent theorem compiled; the final axiom audit is:

    'Q0Root52.safe_root' depends on axioms: [propext, Classical.choice, Quot.sound]

No native_decide, sorryAx, or external search correctness premise. The initial monolithic long trace in shard20 was killed at the memory limit; the separately checked sparse trace and the rebuilt shard20 passed. The compiled module has exact parent table and bound above. The generated final parent Lean source SHA256 is c0e1949b10a1e130fc74351872b65490e98206c634ef6b10a87fbf90c014ee48.

Reproduction: unpack the two pinned artifacts; compile TwoSidedAutomata, Q0ExhaustiveTree, Q0Trace; run `python generate_q0_exhaustive_lean.py /path/to/rocq52 /path/to/lean52`; compile Q0Root52Base, Q0Root52Long, all Q0Root52Shard0..23, then Q0Root52Parent using the pinned core on LEAN_PATH. Keep parallelism at 1–2 under memory cap. [Q0RosterConsume.lean](Q0RosterConsume.lean) is a kernel-checked exact-table filtering/lifting theorem suitable for the Raw11 route; the concrete consumer is separate.
