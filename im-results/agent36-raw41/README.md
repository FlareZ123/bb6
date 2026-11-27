# Raw41 descendant coverage

Child 005 (A1=0LB, B1=1LB): `1RB0LB_1RC1LB_0RD---_1LD1RA_------_------`. Deterministic original enumeration: 493 open leaves; 487 FAR certificates and six new pumping certificates at indices 17,110,198,199,292,349. All six compile with original Agent46AutoPump against accepted Canonical77 artifact 14997966221, axioms propext/Quot.sound. Exhaustive weighted-cover assembly at 207 is in progress, not yet claimed. Decode the archive via base64 -d | tar -xJ from Agent47's Raw41 working directory, then use the original gen_auto.py and gen_children.py. Archive SHA256 1cfafac1026ee321f0d0303d7656db8fe0be354c7455c9da536c96eb505883ad. The conversion of symbolic left sweeps swaps both left/right prefixes and tails to match Lean's Action.left convention.

Child 001,004,018 and additional unclosed descendants under investigation. No global upper bound claimed.

## Accepted complete child005

All 24 generated branches and `Raw41LB1LBClosed` have compiled against the accepted canonical77 artifact (SHA256 b55e4c939da70aaa4d2f50f5721b9183ab776682f1b682f647ee27aa6cc5da17). `Raw41LB1LB_bound` has only propext, Classical.choice, Quot.sound. `Raw41LB1LBGraft.lean` is also checked, uniquely identifies child005 in the original 153-entry Raw41 local canonical roster and proves a sound 152-entry remainder at weighted bound 207. This is a local descendant reduction, independent of six previously closed children; it does not update the global canonical64 count. Reproduce from Agent47 Raw41 working directory: generate the two-cut and original canonical enumeration, extract child005 fixture, `python gen_children.py survey/005 Raw41LB1LB 207 '1RB0LB_1RC1LB_0RD---_1LD1RA_------_------'`, then compile Auto, Base, all 24 Branch modules, Closed, and Graft with the original checker and core dependencies.

## Additional complete candidate trees (five descendants)

Archive SHA256 `7235abeb3cc0324cd0b4f6a2c0a17f8ddd00fbf32a8443cef22e9c75b441ca35`. Contains FAR and exact symbolic pump fixtures, plus Raw41LC1RE52.lean and manual proof map. Extract into Agent47's Raw41 working directory. Enumerate each literal table in corresponding survey directory and run original gen_children.py with below name/bound/table. Compile Agent46AutoPump (and Agent46Auto2 for nested counter), Auto, Base, each 24 Branch and Closed. At this checkpoint child001 fully source-kernel accepted; 004/009/018/022 have complete candidate trees, not all final builds yet. Nested counter leaf52 already individually kernel accepted; inner F(k,m+1)→F(k+1,m) costs 40k+52, reset F(k,0)→F(0,4k+7) costs 84k+151; entry t67 F(0,3). All compatibility completions covered by its never theorem, ordinary axioms only. F(k,m) right word 00 (10001000)^k (10)^(m+2) 1, left empty, state A.

| Index | Module | Bound | FAR | Auto | Manual | Table |
|---|---|---:|---:|---:|---:|---|
| 001 | Raw41LB0LD | 214 | 159 | 9 | 0 | `1RB0LB_1RC0LD_0RD---_1LD1RA_------_------` |
| 004 | Raw41LB0RE | 137 | 379 | 12 | 0 | `1RB0LB_1RC0RE_0RD---_1LD1RA_------_------` |
| 009 | Raw41LB1RE | 564 | 600 | 17 | 0 | `1RB0LB_1RC1RE_0RD---_1LD1RA_------_------` |
| 018 | Raw41LC1RE | 673 | 374 | 8 | 1 | `1RB0LC_1RC---_0RD1RE_1LD1RA_------_------` |
| 022 | Raw41LD0RE | 184 | 355 | 17 | 0 | `1RB0LD_1RC0RE_0RD---_1LD1RA_------_------` |



## 27 November 2026: 153-cylinder screening and new candidate proof-source

New [screen_canonical.py](screen_canonical.py) reuses the original Agent47 two-query partition and Agent19 canonical enumerator, screens all 153 canonical children in four opt-in CI shards, excluding fourteen previously selected descendants. All 139 new screenings completed without timeout in [CI 46078926057](https://github.com/FlareZ123/bb6/actions/runs/46078926057). The smallest open-leaf count is ten, at **canonical child 088**, table **1RB1LB_1RC1LC_0RD---_1LD1RA_------_------**.

Its exact finite-prefix tree had ten open leaves and candidate weighted maximum 41. [Source-generation CI 46079291525](https://github.com/FlareZ123/bb6/actions/runs/46079291525) produced ten independently recomputable FAR witnesses (one per leaf), and Agent47's source generator emitted 24 exhaustive canonical branches plus Raw41New088Closed.lean. The complete generated source is in artifact raw41-target-88 (ID 15236143725). This is a **candidate complete weighted Cover**, not yet an accepted proof. Original-source Lean checking has been submitted in CI 46079427793.

An early exploratory search accidentally fed underscore-delimited display tables to a FAR backend that expects undelimited 36-character tables. Those initial candidates were invalid and superseded. [close_candidate.py](close_candidate.py) now strips separators; Agent47's independent source generator successfully reconstructed all ten corrected FAR witnesses.

A second candidate, child084 (1RB1LB_1RC0RC_0RD---_1LD1RA_------_------), has 49 open leaves, of which 46 have corrected FAR search witnesses ([CI 46079295993](https://github.com/FlareZ123/bb6/actions/runs/46079295993)); three remain unresolved. Its candidate maximum is 737. Do not count child084 as closed or confuse these local children with the global Canonical40 quotient interface.
