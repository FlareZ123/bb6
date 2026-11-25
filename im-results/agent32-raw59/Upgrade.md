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

All candidate sets disjoint relative to the baseline. Counts are candidate reductions, not source-accepted coverage. The largest sparse candidate (0LF 1530, 92189 states) is deliberately retained until row sharding is available. Sweep reconstruction may also fail; if it does, the generator retains that leaf. No universal branch is claimed.

The compact manifests are gzip/base64; python upgrade_data.py decodes the actual entries. IDs are bound by the original source enumerator's SHA checks. Sweep generator uses the existing exact arbitrary-tail sweep induction, including the blank-entry equality, and sparse certificates use the independent-width checker. The existing partial audit's typed .proven constructor consumes only original-source nonhalting theorems. The new --upgrade flag writes separate Upgrade source modules and preserves the previously accepted baseline. Target UpgradeAll, or Upgrade1LB etc in the existing manual workflow.

Initial asymmetric pilot run 45559896528: Asym1LE and Asym1LB completed successfully; Asym0LB still running at this checkpoint. Prior accepted return-family proofs are not counted here unless the upgrade actually consumes them.
