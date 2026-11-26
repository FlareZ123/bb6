# q0 sibling-root candidate scan — 2026-11-26

**Status: exploratory computational output only.** This scan does not prove the remaining machines nonhalting. It runs the existing `coarse-pair.cjs` search with open leaves retained for q0 active roots 33, 34, 39, 44, 46, 48, 49, and 51.

The full machine tables and open-leaf multiplicities are preserved in [`q0-sibling-scan-2026-11-26.json`](q0-sibling-scan-2026-11-26.json).

| q0 active index | holes | fresh | tree nodes | open leaves | bound (= max halt + 6) | distinct open tables |
|---:|---:|---:|---:|---:|---:|---:|
| 33 | 4 | 5 | 985 | 1 | 162 | 1 |
| 34 | 4 | 5 | 1777 | 4 | 81 | 4 |
| 39 | 4 | 5 | 1873 | 16 | 144 | 16 |
| 44 | 4 | 5 | 2041 | 5 | 90 | 5 |
| 46 | 4 | 5 | 2017 | 1 | 64 | 1 |
| 48 | 4 | 6 | 3745 | 2 | 151 | 2 |
| 49 | 4 | 6 | 5785 | 21 | 234 | 21 |
| 51 | 4 | 6 | 4393 | 31 | 208 | 31 |

## Best next candidates

- **Root 33** has one open leaf. Its partial table is `1RB1RD1RC0RE0LA---1LA1LD0LF0RB1LF0LC`. The sole undefined transition is C1. A separate one-million-step simulation did not reach C1.
- **Root 46** has one open leaf. Its partial table is `1RB1RD1RC0RE0LA1RF1LA1LD1RC1LE---0RB`. The sole undefined transition is F0. A separate one-million-step simulation did not reach F0.

These are empirical reachability observations, not infinite-run proofs. The next mathematical task is to find an inductive configuration/tape invariant proving the missing transition is unreachable, or construct a source-level progress family analogous to the row26/row28 sweep proofs.

## Search summary

- Roots 33 and 46: one open leaf each; strongest immediate candidates for a direct nonhalting-cylinder proof.
- Root 48: two open leaves.
- Roots 34 and 44: four and five open leaves.
- Roots 39, 49, and 51: 16, 21, and 31 open leaves respectively.

The search itself completed successfully in CI. The Node-only workflow target initially had an unrelated final-assumptions step failure; a subsequent run succeeded and emitted the full JSON artifact.
