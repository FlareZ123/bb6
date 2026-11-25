# Champion-containing residual frontier

## Target cylinder

This investigation isolates the retained 9-hole residual

`1RB---_1RC---_1LD---_------_------_------`

which is canonical index 99 / raw residual index 139 in the 121-entry roster. It is compatible with the published six-state champion and is retained in Agent 47's 109-entry roster. It is outside the 19-parent first-hole sweep currently recorded in `im-results/agent47-rooted-tnf/RootSiblingFirstHole.lean`.

The Lean source constructs the cylinder directly from the first-one root by fixing B/0 = 1RC and C/0 = 1LD. The initial undefined transition is D/1.

## Champion path and terminal leaf

The successive first-hole queries along the champion-compatible path are:

| Parent depth | First hole | Champion move | Known successful moves |
|---:|---|---|---:|
| 0 | D/1 | 0LE | 3 |
| 1 | E/1 | 1RC | 4 |
| 2 | E/0 | 0LD | 7 |
| 3 | D/0 | 1RA | 8 |
| 4 | C/1 | 0RF | 11 |
| 5 | F/1 | 0RE | 12 |
| 6 | F/0 | 1RA | 53 |
| 7 | A/1 | 1RA | 213 |

After these eight ordinary refinements, the only missing transition is B/1. The default completion of that partial table is exactly the published champion table. The proof transports the exact theorem `champion_halts_exact` through `weightedTNF_halt_iff_firstHole`, then closes the one-hole cylinder with `WeightedTNFCertificate.lastHole` at

`championScore = proposedTM63Moves + 7`.

This is stronger than a singleton leaf: every ordinary completion at B/1 is a total machine with no halting transition, while the halt completion is bounded at the champion score.

## Sibling closures

A bounded search produced 28 candidate side-cycle/lasso witnesses across the eight earlier splits. Their counts by depth are:

`0, 1, 3, 8, 7, 9, 0, 0`.

The Lean theorem `championWitnessesOK` replays every witness against the corresponding partial child using `residualWitnessOK`; the frontier does not trust the search output without this check.

The resulting `RootedFrontier` leaves **156 open residual cylinders**. The 28 side-cycle/lasso children, the eight immediate halt branches, and the final one-hole champion cylinder are closed. The residual frontier is a valid partial upper-bound decomposition at the champion score, not a complete upper-bound proof.

## Integration with the 109-roster

The source proves that the target cylinder is exactly one of the 109 retained residuals. Replacing that one entry with the 156 open descendants yields a 264-entry roster:

- 108 untouched residual obligations;
- 156 descendants of the champion-containing cylinder.

`championResidualRefinedRosterSound` gives the mixed-bound dichotomy at the champion score. Consequently, `exactBB6OfChampionResidualRoster` reduces exact BB(6) to supplying a `Cover (WeightedBound championScore)` for each of those 264 residuals.

## Source and verification

- Lean source: `ChampionResidualFrontier.lean`
- CI workflow: `.github/workflows/agent6-champion-residual.yml`
- Key theorems: `championP8Certificate`, `championResidualFrontierSound`, `championResidualRefinedRosterSound`, `exactBB6OfChampionResidualRoster`

The finite witness search is heuristic; the Lean replay theorem is the proof-bearing check. The exact champion halt theorem is imported from Agent 48's counted-inc0 source closure. This directory is intermediate research and therefore belongs in `im-results/`, not `results/`.

## Follow-on depth-7 scan

A separate bounded scan of the 23 ordinary A/1 siblings at depth 7 found that 15 reach the remaining B/1 hole after 214–3506 successful moves. These are strong candidates for one-hole `lastHole` certificates at the champion score; they are not yet incorporated into the 156-leaf Lean frontier. The other eight (`0LA, 0LC, 1LC, 1LD, 1RD, 0LE, 1RE, 1LF`) neither reached B/1 within one million moves nor yielded a side-cycle witness under the scan's small bounds; a deeper five-million-step run with entry ≤ 20, period ≤ 50, and boundary radius ≤ 50 also left all eight unresolved. They remain unresolved, not proven nonhalting. See [p7-last-hole-scan.md](p7-last-hole-scan.md).

The current frontier's completion-mass accounting is:
- original 9-hole cylinder: `25^9 = 3,814,697,265,625`;
- 156 open residuals: `3,648,834,608,700`;
- closed mass: `165,862,656,925` (about 4.35%).

Thus the frontier is a valid champion-score decomposition but closes only about 4.35% of the cylinder's raw completion mass. The depth-7 scan is a useful next refinement, not a resolution of the remaining mass.
