# Canonical58 upstream holdout intersection (intermediate)

**Status:** metadata-level routing crosswalk only. This is not a Lean theorem, a Cover, or a reduction of the Canonical58 residual count.

## Inputs and method

The reproducible script crosswalk.py reads:

- im-results/agent10-nov26-cryptids/holdout-source-crosswalk.tsv (56 upstream source-table matches);
- im-results/agent13-roster-convergence/canonical-124.json (the 124-entry root residual export).

It reproduces the canonicalAddress 2 state-introduction filter, then removes the 38 raw residual indices consumed by the current path: Combined106 (18), Raw107/Raw114 (2), the Canonical68 stable batch (8), Raw71/Raw77/Raw81 (3), Raw120 (1), the five-parent Canonical59 batch (5), and Raw113 (1). The reconstructed set has 58 distinct entries and retains Raw59 while excluding Raw118, consistent with the accepted [Canonical59 five-parent integration](../../results/2026-11-26-canonical59-five-parent-integration-agent31.md) and [Canonical58 Raw113 delta](../../results/2026-11-26-canonical58-raw113-delta-agent17.md). This remains a metadata reconstruction rather than a direct export of the accepted Lean roster.

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

## Reproduction run

The earlier script and report schema were reproduced successfully by workflow run 45899546150 on head 3731bd0ce6365a815473f0d23c96c00c0a2a551b (superseding the earlier validation run 45898819353). The job ran Python syntax compilation and the full crosswalk script, then asserted the 58-entry roster count, 56 unique matches, zero unmatched/ambiguous rows, the eight expected residual groups, and 1,400 distinct leaf completions.

The uploaded artifact is canonical58-source-crosswalk (artifact ID 15154733821, 6,866 bytes, SHA-256 415ec5d21e19373490bfa87167027d142d66e468bff87096a2f3e2d02d73f053). The report records the input Git blob SHAs. That historical run checked the count but missed a one-for-one Raw59/Raw118 substitution. The corrected script requires unique retained IDs, Raw59 present and Raw118 absent. The corrected committed JSON was independently recomputed from the same two pinned input blobs with JavaScript: all 56 unique matches, eight parent groups, and 1,400 distinct completion cylinders are unchanged. The prior artifact is historical and does not contain this correction. The corrected Python script and its explicit Raw59-retained/Raw118-absent guards passed the existing `canonical58-source-crosswalk` workflow in run [45904827205](https://github.com/FlareZ123/bb6/actions/runs/45904827205), on source head `5a7975e82552108747d32d32825e8c40cdaf2dd6`. The successful report artifact is `canonical58-source-crosswalk` (ID `15157486592`, SHA-256 `5c14847f5da0fe0598f6b85406cc6b1c51debf216eb3e0d37cffa38faa64adbe`). This validates the metadata-level Python reconstruction and identity guards; it is still not a Lean roster-export audit or a Cover.

## Proof status and limits

The crosswalk identifies where historical source leaves sit; it does not establish that their source modules have passed local source audit or that the corresponding parent residual is covered.

Agent10's current dossier records Raw140 n4/n5 as the two locally source-accepted 25-completion NonHalt leaf Covers (run 45894023420). Raw140 n19/n20 are queued; n8/n12/n16 and Pairs2–9 remain drafts pending source audit. All eight Halt rows (including three newly added rows) need primitive-score bounds before weighted ingestion. Baseline-191 source status is not inferred here.

The two accepted Raw140 leaves cover 50 of 25^9 completions of current raw residual 140. No parent is closed, and the Canonical58 count does not change. Use this crosswalk to route source transfer or finite refinement work, not to claim a global reduction.

Run from the repository root with:

    python im-results/agent31-canonical58-source-crosswalk/crosswalk.py

The script writes crosswalk.json, including input Git blob SHA values, exact row-to-ancestor matches, group counts, and completion-cylinder unions. A future formal integration must still prove the roster correspondence and source Covers in Lean.
