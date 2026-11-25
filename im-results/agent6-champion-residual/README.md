# Champion-containing residual frontier

## Target cylinder

This investigation isolates the retained 9-hole residual

`1RB---_1RC---_1LD---_------_------_------`

which is raw residual index 139. It is canonical index 99 in the older 121-entry roster and canonical index 102 in the newer 124-entry manifest used by Agent 47's 78-way quotient frontier. It is compatible with the published six-state champion, retained in the 109-entry roster, and not among the 28 symmetry-discarded indices or 18 early-bound cuts in the 78-way roster. It is outside the 19-parent first-hole sweep currently recorded in `im-results/agent47-rooted-tnf/RootSiblingFirstHole.lean`.

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

## Canonical 78 and parent-certificate integration (draft)

The newer quotient route reduces the 124 raw residuals to 96 canonical addresses and then to 78 retained quotient-compatible representatives. The manifest identifies this champion cylinder as canonical index 102 / raw index 139, address B0=1RC, C0=1LD. The exact Lean pair-membership check is included in `ChampionResidualParentIntegration.lean`.

Agent 48's two-hole A/1–B/1 parent certificate is intended to replace only the final `championStep 7` of this frontier. That step has 23 ordinary non-champion children and no depth-7 side-witness entries. The earlier seven splits contribute the other 133 open leaves. If the parent certificate is proved equal to `championP7`, the integrated frontier should therefore have **133** residual leaves, not zero.

The integration draft:
- proves `BB6.Agent48Parent.parent = BB6.Agent6ChampionResidual.championP7` slot by slot;
- transports the parent certificate to `championP7` and replaces the final A/1 split by a closed frontier node;
- proves every open frontier leaf occurs in the explicit residual list and derives a root `Cover` from Covers for all 133 leaves;
- proves the raw139 address/table is exactly present in the canonical 78 roster;
- provides a conditional `ExactBB6 championScore` theorem from Covers for every nonchampion roster entry plus the 133 raw139 frontier leaves; it also checks the address count 77 + 133 = 210.

The parent certificate dependency is now source-accepted in [45539867315](https://github.com/FlareZ123/bb6/actions/runs/45539867315), and the canonical78 exact-witness wrapper is being audited in [45539884311](https://github.com/FlareZ123/bb6/actions/runs/45539884311). The expanded Agent6 integration draft has not yet been source-accepted; the workflow includes it and should be dispatched after the canonical78 wrapper passes. The earlier 109-roster accounting (108 untouched + 156 descendants = 264) is a separate raw-roster specialization and must not be conflated with the 78-way quotient accounting.


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
