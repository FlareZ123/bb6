# Agent 10: 56 archived holdouts match pinned Cryptids source proofs

I compared the 663 archived BB(6) holdouts with the 64-parent canonical roster and the 212 BB(6) Halt/NonHalt modules at `google-deepmind/cryptids@d1d231afe3a5f6310ac9f956d5687b5a45d7a13d`. The comparison uses all 24 A/B-fixing permutations and requires exact agreement on every assigned transition, with each holdout hole matched by an upstream HHH row.

**Result: 56 distinct holdout rows match 56 distinct upstream modules**, with no row or module duplicates: 48 NonHalt and 8 Halt, across eight parent IDs:

| Raw parent | Historical holdouts | Source matches | NonHalt | Halt |
|---:|---:|---:|---:|---:|
| 8 | 54 | 4 | 3 | 1 |
| 9 | 128 | 9 | 7 | 2 |
| 10 | 260 | 19 | 16 | 3 |
| 13 | 22 | 1 | 1 | 0 |
| 23 | 20 | 4 | 3 | 1 |
| 134 | 7 | 1 | 1 | 0 |
| 139 | 67 | 11 | 10 | 1 |
| 140 | 41 | 7 | 7 | 0 |

The 56 are exactly 35 modules already in the baseline 191-module inventory plus the 21 November 26 additions. The TSV records parent, holdout/source RLE, source path, blob SHA, batch, and first-use schedules where available:
`im-results/agent10-nov26-cryptids/holdout-source-crosswalk.tsv`.

**Scope warning:** these are matches to the historical 663 list, not a statement that all 56 are leaves in today's pruned Canonical59 residual queue. Check each candidate against the current parent/queue before counting it as usable work. The 48 nonhalting modules are potential 25-completion leaf Covers once their local source bridges are accepted; the 8 halting modules still need primitive-step score bounds. No parent Cover or global count reduction follows from this crosswalk.

Raw140 is the immediate pilot: 7/41 historical holdouts match, all NonHalt. Pair1's two leaves passed local source CI (run 45894023420); Pair10's two older matches are in a weighted first-hole bridge awaiting CI.
