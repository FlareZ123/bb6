# Raw11 first-D crosswalk: q0 checkpoint, q0 automata, and q32

**Status:** intermediate structural result. This is a finite transition-table crosswalk, not a global BB(6) cover.

## Main result

The Raw11 first-D cut has 116 residual frontier entries. The exact q0 checkpoint export has 156 active plus one held row. Comparing their 12 transition slots gives:

- **141 of 157** q0 checkpoint rows refine exactly one Raw11 frontier entry.
- The remaining **16** divide into:
  - **10 rows** incompatible with every one of the 116 frontier entries;
  - **6 rows** that are coarser residual parents of exactly four frontier entries each.

The six four-way complements are:

| q0 checkpoint row | Raw11 frontier indices |
|---:|---:|
| 138 | 100–103 |
| 140 | 90–93 |
| 141 | 95–98 |
| 142 | 104–107 |
| 143 | 109–112 |
| 154 | 14–17 |

The ten no-overlap rows are checkpoint indices 136, 137, 139, 144, 145, 146, 147, 152, 153, and 155. They are all descendants of the Raw11 parent. The accompanying Lean development proves that their fixed first-three-state conflicts exclude quotient-compatible membership in any first-D frontier entry; therefore every completion of each row lies in the Raw11 (\mathrm{WeightedBound}(18)\) branch.

For the six coarse rows, the Lean theorem retains the exact four-entry frontier complement rather than falsely closing them.

## Existing certified leaf families routed into the same cut

- All **94 q0 open-automata leaves** refine Raw11 frontier entry 115 (the A1=1RD cylinder). They refine exactly nine q0 checkpoint rows: 26 (13 leaves), 33 (1), 34 (4), 39 (16), 44 (5), 46 (1), 48 (2), 49 (21), and 51 (31).
- The q32 queue has 84 rows: 14 refine frontier entry 114 and 70 refine entry 115.
- The 32 q32 SWside leaves split 2 under entry 114 and 30 under entry 115.
- The 94 q0 automata leaves are pairwise disjoint; the 32 q32 SWside leaves are pairwise disjoint; and the two families are mutually disjoint.

## Interpretation and limitation

This identifies a concrete Raw11-to-q0 partition edge. It does **not** show that the 94 q0 automata leaves cover the whole A1=1RD cylinder, nor that the 157-row checkpoint is a complete Raw11 partition. The checkpoint rows are residual obligations. The exact useful reduction is:

1. 141 checkpoint rows are already nested in eight Raw11 frontier entries;
2. ten unmatched rows are targeted for closure at bound 18 by the Raw11 cut (formal proof pending CI);
3. six unmatched rows retain only the four-entry complements listed above;
4. the q0 and q32 closed leaf families can be routed into frontier entries 114/115 without overlap.

The remaining frontier obligations still require source-accepted coverage. In particular, the q0 automata bank's original Rocq source integration remains separate from its Lean finite-automata checking.

## Reproduction

Run:

```sh
node im-results/agent24-raw11-q0-graft/crosswalk.cjs
```

The script checks the exact counts, all table containment/compatibility relations, the 16 unmatched checkpoint rows, the six four-way complements, and pairwise disjointness. Its machine-readable output is in [crosswalk.json](crosswalk.json).

The quotient-aware Lean proof development is in [Raw11Q0CheckpointGraft.lean](Raw11Q0CheckpointGraft.lean). It imports the Raw11 first-D cut directly and attempts to prove the ten bound-18 closures while exposing the six retained four-way complements. The script and Lean development are deliberately kept in `im-results/`; this is not yet a publishable BB(6) upper-bound result. CI acceptance is pending.
