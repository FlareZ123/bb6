# Canonical58 upstream holdout intersection (intermediate)

**Status:** metadata-level routing crosswalk only. This is not a Lean theorem, a Cover, or a reduction of the Canonical58 residual count.

## Inputs and method

The reproducible script crosswalk.py reads:

- im-results/agent10-nov26-cryptids/holdout-source-crosswalk.tsv (56 upstream source-table matches);
- im-results/agent13-roster-convergence/canonical-124.json (the 124-entry root residual export).

It reproduces the canonicalAddress 2 state-introduction filter, then removes the 38 raw residual indices consumed by the current path: Combined106 (18), Raw107/Raw114 (2), the Canonical68 stable batch (8), Raw71/Raw77/Raw81 (3), Raw120 (1), the five-parent Canonical59 batch (5), and Raw113 (1). The resulting set has 58 entries, matching the accepted Canonical58 count.

Each one-hole TSV table is checked for extension of a current residual. All 56 rows have exactly one unique current ancestor. The script also enumerates the 25 possible completions of each one-hole table and counts their union within each residual.

## Intersection

| Current raw residual | Canonical index | Holes | Address | All rows | Nov26-21 | baseline-191 | NonHalt | Halt | Distinct leaf completions |
|---:|---:|---:|---|---:|---:|---:|---:|---:|---:|
| 8 | 4 | 10 | 0LC | 4 | 2 | 2 | 3 | 1 | 100 |
| 9 | 5 | 10 | 0RC | 9 | 4 | 5 | 7 | 2 | 225 |
| 10 | 6 | 10 | 1LC | 19 | 7 | 12 | 16 | 3 | 475 |
| 13 | 8 | 9 | 1RC, 1LA | 1 | 1 | 0 | 1 | 0 | 25 |
| 23 | 13 | 9 | 1RC, 0LD | 4 | 0 | 4 | 3 | 1 | 100 |
| 134 | 97 | 8 | 1RC, 0RD, 1RE | 1 | 0 | 1 | 1 | 0 | 25 |
| 139 | 102 | 9 | 1RC, 1LD | 11 | 2 | 9 | 10 | 1 | 275 |
| 140 | 103 | 9 | 1RC, 1RD | 7 | 5 | 2 | 7 | 0 | 175 |

The 21 new Nov26-21 rows lie under six residuals (8, 9, 10, 13, 139, 140). The 35 baseline-191 rows add residuals 23 and 134 and increase the counts under the other six. In total, the 56 one-hole cylinders account for 1,400 distinct complete tables across these eight residuals. The largest group, raw10, accounts for 475 of 25^10 completions.

## Proof status and limits

The crosswalk identifies where historical source leaves sit; it does not establish that their source modules have passed local source audit or that the corresponding parent residual is covered.

Agent10's current dossier records Raw140 n4/n5 as the two locally source-accepted 25-completion NonHalt leaf Covers (run 45894023420). Raw140 n19/n20 are queued; n8/n12/n16 and Pairs2–9 remain drafts pending source audit. The three Halt rows need primitive-score bounds before weighted ingestion. Baseline-191 source status is not inferred here.

The two accepted Raw140 leaves cover 50 of 25^9 completions of current raw residual 140. No parent is closed, and the Canonical58 count does not change. Use this crosswalk to route source transfer or finite refinement work, not to claim a global reduction.

Run from the repository root with:

    python im-results/agent31-canonical58-source-crosswalk/crosswalk.py

The script writes crosswalk.json, including input SHA-256 values, exact row-to-ancestor matches, group counts, and completion-cylinder unions. A future formal integration must still prove the roster correspondence and source Covers in Lean.
