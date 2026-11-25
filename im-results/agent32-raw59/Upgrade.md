# Raw59 candidate reduction, 2026-11-25

Baseline: prior checked partial audits in run 45547813131, source c8aa2607ad4711501e18e0943eec70e9475fd834. Retrieved all seven exact residual artifacts and matched them against the SHA-pinned enumeration.

| child | baseline residuals | new sparse-window candidates | new sweep candidates | prospective remainder |
|---|---:|---:|---:|---:|
| 0LA | 242 | 52 | 27 | 163 |
| 0LB | 35 | 18 | 6 | 11 |
| 0LE | 160 | 10 | 132 | 18 |
| 0LF | 149 | 40 | 0 | 109 |
| 1LB | 46 | 13 | 27 | 6 |
| 1LE | 34 | 5 | 22 | 7 |
| 1LF | 65 | 3 | 0 | 62 |
| Total | 731 | 141 | 214 | 376 |

### Final six known 1LB candidates

[Raw59LB1Sweep1734.lean](Raw59LB1Sweep1734.lean) gives the exact partial table `1RB1LB_1RC1RF_0RD0LE_1LD1RE_---1LA_0RA0RB` (E/0 unassigned), open index 1734 in the SHA-pinned 1LB enumeration. In the existing zipper convention (head at the first bit of the left list), define D(n) with left word `0 (011)^(n+2) (01)^(4(n+1))` and empty right list. The blank run reaches D(0) after 104 steps. For every n, D(n) returns to D(n+1) after exactly `120(n+1)+101` steps. The proof composes two exact left/right sweep pairs: 4-step `10` transfer, 17-step framed `110 -> 010`, 12-step `1010 -> 0101`, and 3-step `100 -> 011` transfers, with arbitrary untouched tails. Entry and growth compile locally with Lean 4.36.0-rc2 against the copied computational SweepPumping core (axioms: propext and Quot.sound only). The original-source `never` bridge passed [run 45632801815](https://github.com/FlareZ123/bb6/actions/runs/45632801815). The earlier sweep for 583 passed [run 45595774004](https://github.com/FlareZ123/bb6/actions/runs/45595774004). The upgrade generator binds the certificate to the SHA-pinned exact leaf; only source acceptance of the full audit permits removing it from the retained complement. This additional candidate is not included in the earlier table. No new parent or global coverage count is claimed.

The four other exact retained indices are 189, 190, 191 and 194 (F/0 remains unassigned; E/0 is respectively 1LA, 1LC, 1LD, 1RD in the common table `1RB1LB_1RC0LB_0RD0RF_1LD1RE_???1LA_---1RA`). The existing two-sided DFA witnesses for 189 and 191 close under saturation (873 and 888 abstract configurations, 117 edges each). The two previously unresolved leaves now have one-sided block-FAR witnesses from the forward saturation algorithm:

| Index | Block width | Run cap | Run modulus | Retained runs | Left states before quotient | NFA nodes before quotient |
|---|---:|---:|---:|---:|---:|---:|
| 190 | 4 | 1 | 7 | 6 | 434 | 1321 |
| 194 | 2 | 3 | 2 | 3 | 51 | 448 |

Unreflected in both cases. The larger width-six witness for 190 also closed (cap 2, modulus 2, five runs), but width four has a smaller source proof. `generate_lb1_four.py` deterministically generates the finite checker witnesses, original coverage adapters and previous rungram certificates. The updated SHA-pinned audit generator binds all four exact tables to their leaf indices. [Source verification run 45657895022](https://github.com/FlareZ123/bb6/actions/runs/45657895022) targets the four leaves; full 1LB audit still required. These candidate results are not yet a closed source-checked parent.

All candidate sets disjoint relative to the baseline. Counts are candidate reductions, not source-accepted coverage. The largest sparse candidate (0LF 1530, 92189 states) is deliberately retained until row sharding is available. Sweep reconstruction may also fail; if it does, the generator retains that leaf. No universal branch is claimed.

The compact manifests are gzip/base64; python upgrade_data.py decodes the actual entries. IDs are bound by the original source enumerator's SHA checks. Sweep generator uses the existing exact arbitrary-tail sweep induction, including the blank-entry equality, and sparse certificates use the independent-width checker. The existing partial audit's typed .proven constructor consumes only original-source nonhalting theorems. The new --upgrade flag writes separate Upgrade source modules and preserves the previously accepted baseline. Target UpgradeAll, or Upgrade1LB etc in the existing manual workflow.

Initial asymmetric pilot [run 45559896528](https://github.com/FlareZ123/bb6/actions/runs/45559896528) completed successfully. Prior accepted return-family proofs are not counted here unless the upgrade actually consumes them.
