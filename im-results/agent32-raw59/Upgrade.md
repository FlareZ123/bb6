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

### Two-sweep candidate for 1LB/1734

[Raw59LB1Sweep1734.lean](Raw59LB1Sweep1734.lean) gives the exact partial table `1RB1LB_1RC1RF_0RD0LE_1LD1RE_---1LA_0RA0RB` (E/0 unassigned), open index 1734 in the SHA-pinned 1LB enumeration. In the existing zipper convention (head at the first bit of the left list), define D(n) with left word `0 (011)^(n+2) (01)^(4(n+1))` and empty right list. The blank run reaches D(0) after 104 steps. For every n, D(n) returns to D(n+1) after exactly `120(n+1)+101` steps. The proof composes two exact left/right sweep pairs: 4-step `10` transfer, 17-step framed `110 -> 010`, 12-step `1010 -> 0101`, and 3-step `100 -> 011` transfers, with arbitrary untouched tails. Entry and growth compile locally with Lean 4.36.0-rc2 against the copied computational SweepPumping core (axioms: propext and Quot.sound only). The original-source `never` bridge has been dispatched with the existing workflow selector `LB1Sweep1734`. The upgrade generator binds the certificate to the SHA-pinned exact leaf; only source acceptance of the full audit permits removing it from the retained complement. This additional candidate is not included in the earlier table. No new parent or global coverage count is claimed.

All candidate sets disjoint relative to the baseline. Counts are candidate reductions, not source-accepted coverage. The largest sparse candidate (0LF 1530, 92189 states) is deliberately retained until row sharding is available. Sweep reconstruction may also fail; if it does, the generator retains that leaf. No universal branch is claimed.

The compact manifests are gzip/base64; python upgrade_data.py decodes the actual entries. IDs are bound by the original source enumerator's SHA checks. Sweep generator uses the existing exact arbitrary-tail sweep induction, including the blank-entry equality, and sparse certificates use the independent-width checker. The existing partial audit's typed .proven constructor consumes only original-source nonhalting theorems. The new --upgrade flag writes separate Upgrade source modules and preserves the previously accepted baseline. Target UpgradeAll, or Upgrade1LB etc in the existing manual workflow.

Initial asymmetric pilot run 45559896528: Asym1LE and Asym1LB completed successfully; Asym0LB still running at this checkpoint. Prior accepted return-family proofs are not counted here unless the upgrade actually consumes them.
