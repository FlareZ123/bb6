# Raw11 conditional parent coverage

**Current locally kernel-checked interface: 227 residual cylinders at any common bound B ≥ 4663.** The original Raw11 parent is `1RB---_1RC---_0LA---_------_------_------`. No complete Raw11 Cover or BB(6) upper bound follows yet. The last CI-accepted interface has 237 residuals; the ten additional Covers described below were compiled locally against its immutable accepted dependency artifacts.

## Exact route and consumers

The original route, `Raw11Route.lean`, refines Raw11 using 38 first-hole splits, 306 translated-cycle leaves and 54 automata leaves. Its 299 retained tables comprise all 157 q0 checkpoint targets (156 active and one held) and 142 extra cylinders. `PhaseFrontier.lean` gives a sound mixed-tree consumer using the existing `PhaseTree.sound`, explicitly checking first-hole queries, support, and exact table equality before accepting certified leaves. Each removal below preserves the precise remaining roster; the cap can be lifted to the common champion bound.

| Stage | Exact retained count | Evidence |
|---|---:|---|
| Raw11 route | 299 | `Raw11Route.lean`, [CI 45872082943](https://github.com/FlareZ123/bb6/actions/runs/45872082943) |
| Seven q0 roots (26,34,39,44,46,48,52) | 292 | `Raw11Root39Consume.lean`, `Raw11Root52Consume.lean`, [CI 45873233270](https://github.com/FlareZ123/bb6/actions/runs/45873233270) |
| 46 extra Covers | 246 | `Raw11Root52ExtrasConsume.lean`, [CI 45906697676](https://github.com/FlareZ123/bb6/actions/runs/45906697676) |
| Three additional q0 parents (33,49,51) | 243 | `Raw11Root52Q0ParentsConsume.lean`, same CI |
| Six capped extra parents (126–130,137) | 237 | `Raw11Root52CappedParentsConsume.lean`, [CI 45911662010](https://github.com/FlareZ123/bb6/actions/runs/45911662010) |
| Ten translated-cycle q0 parents (136,137,139,144–147,152,153,155) | **227** | `Raw11Q0FreshClosed.lean`, local Lean 4.36.0-rc2, source/olean dependency artifacts below |

The 46 extra Covers comprise 35 complete at-most-four-hole trees (including recurrence-backed 92/124) and eleven five-hole trees 85–90,125,135,136,138,139. The six capped extra parents have respective bounds 167,168,125,214,131,180. Their count must not be confused with q0 indices of the same number. Parent 52 sets the overall local cap 4663. The prior six-q0 bounds are 200,81,144,90,64,151; additional parents 33,49,51 have bounds 162,234,208.

## Exact first-D cut crosswalk and new ten-parent proof

Agent44's independently source-checked [first-D tree](../agent44-raw11-fresh-cut/README.md) retains 116 cylinders. Slotwise comparison of the actual two trees, not merely their frontier lengths, gives:

- 84 extras (indices 0–83) exactly equal 84 distinct first-D entries; the other 58 extras strictly refine entry115 and all fix D0=1LA.
- 141 q0 targets refine eight first-D entries: 24 (116–135), 25 (96–115), 94 (148), 99 (149), 108 (150), 113 (151), 114 (76–95), 115 (0–75 and held 156).
- Six coarser q0 targets contain the 24 first-D entries that have no finer Raw11 target: q0 138 contains 100–103; 140 contains 90–93; 141 contains 95–98; 142 contains 104–107; 143 contains 109–112; 154 contains 14–17. Each has four first-D children; none is closed by this crosswalk.
- The remaining ten q0 targets have no compatible first-D frontier entry because each is an exact translated-cycle leaf of `Raw11FreshCut.audit`. These are the ten rows now consumed at bound 18; earlier descriptions of all 16 as disjoint were incorrect.

The new source independently rechecks all ten actual cycle certificates through the existing `PhaseTree.check` and `PhaseTree.sound` (no new oracle). It proves exact membership in the **237-entry** retained roster and filters by `Q0RosterConsume.removeCovered` (exact table equality), not by unproved containment or count arithmetic. Its exported `cover_from_remaining` composes the prior 237-parent conditional theorem with the ten local Covers, requiring only bounds on the exact remaining 227 tables. The source SHA-256 is `acf4a8226c457b02ea9aa849b02ab6382b3a7a66bcc0b517763dad2a9d154b7d`. Local Lean 4.36.0-rc2 exited 0; all six printed exported theorem profiles are [propext, Classical.choice, Quot.sound], without sorryAx or native_decide. It used immutable artifacts 15159003899 (base closure), 15161045625 (237 consumer), and 15159257293,15154832729,15154568902,15154569169,15154663882,15158958272 (six parents), exactly as the accepted capped-consumer workflow specifies. The compiled wrapper SHA-256 was f22db7764e8f5000698202a00c53e326571f19c70244b393a62984eb2632fe7f.

The 135 open cylinders (58 extras and 77 q0 rows) below first-D entry115 are pairwise incompatible and span 18 of 24 D0 values. The six absent D0 values are 0LA,0RA,0LF,0RF,1LF,1RF; absence alone is not a Cover. Agent5's [q32 nesting map](../agent5-weighted-tnf-queue/entry115-complement-crosswalk.md) relates the 70 entry115 q32 rows to this route, including four independent side-cycle Covers and coarse rows39/47. The complete retained complements of coarse rows39/47 must be preserved; counts alone do not prove exhaustion.

## Outstanding obligations

The immediate remaining extra-parent candidates are 84,131,132,133,134,140; their previous proof attempts and source generators are preserved in the historical record. A parent may be removed only after its exact Cover and membership are established. The six coarser q0 nodes identified above may instead be solved by covering their four first-D children using the exact first-hole split at B1. The remaining 227 roster entries must all be bounded (or refined exhaustively with all complements retained) before the Raw11 parent is closed. No Canonical57 removal is yet justified.

The original Coq checkpoint route is a separate proof system: `Agent47Q0NineParentMembership.v` and `Agent47Raw11RestrictedQ0.v` establish exact membership and restriction identities, with the corrected conditional bridge in `Agent13Raw11Q0Bridge.v`. Nine parent source safety proofs at a common bound 234 were originally sought for the 94 automata bank leaves. The accepted Lean results do not by themselves constitute a Coq queue consumption.

See [historical detailed dossier](HISTORICAL-20261126.md) for older derivations, certificate-generation details and CI records, including the original nine-parent grouping.
