# Raw40: first two query levels, exact partial coverage

Parent `1RB---_1RC---_0RD---_1LD1LA_------_------`, canonical raw40. First unassigned query A1 after six ordinary steps.

## Three new nonhalting families

Each five-hole subcylinder has 25^5 = 9,765,625 arbitrary completions, all nonhalting. The proofs are uniform inductions over exact zipper configurations.

| A1 | Next assigned slot | Entry | Right unary length | Epoch cost |
|---|---|---:|---:|---:|
| 0LA | C1=0RC | 9 | 3n+2 | 6n+13 |
| 1LA | B1=0RD | 8 | 2n+3 | 8n+17 |
| 1LA | B1=1RB | 8 | 4n+3 | 8n+15 |

`Raw40Pump.lean` and `Raw40MorePumps.lean` prove the recurrences and NeverHalts for every compatible completion, using SweepPumping.

## Partial coverage

`Raw40Partial.lean` checks the entire two-query-level audit using the existing PartialAudit / ZipThreeHoleAudit kernel proof. Raw assignment counts include all ordinary and halt values in every unassigned row.

| Terminal type | Count | Raw completions |
|---|---:|---:|
| First halt | 1 | 244,140,625 |
| First-level cycles | 6 | 1,464,843,750 |
| Second halt | 18 | 175,781,250 |
| Second-level cycles | 126 | 1,230,468,750 |
| Three new pumps | 3 | 29,296,875 |
| Remaining five-hole cylinders | 303 | 2,958,984,375 |
| Total | | 6,103,515,625 |

Discharged raw assignment mass: 3,144,531,250 (51.52%). The exact partial-sound theorem is at weighted bound 7014, with all 303 unresolved leaves explicit. The parent occurs once in the accepted canonical77 roster. `Raw40Graft.lean` derives the 379-entry conditional frontier from accepted canonical77 via the quotient graft theorem. This is an exact partial refinement, not a complete closure or an improved global bound.

All four Lean modules compiled locally using Lean 4.36.0-rc2 and coherent original canonical77-certified artifact 14997966221 (CI45554648116). Only propext, Quot.sound, and Classical.choice appear in the printed axiom dependencies. The finite side-cycle candidates came from Agent2's enumerate.cpp with a probe-only modification: run classify on each of the 24 immediate ordinary moves rather than recursing. All candidates are independently kernel-checked. The compact probe witness data is preserved in probe.txt. No new CI result is claimed.
