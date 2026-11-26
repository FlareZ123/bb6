# Raw140: additional pinned upstream nonhalt matches

This is an intermediate routing and proof-integration record, not a parent Cover.

## Exact parent and matching scope

The canonical roster entry is canonical-124 entry 103, raw_residual_index 140, depth 2, with nine holes and fixed rows A0=1RB, B0=1RC, C0=1RD. The archived 2026-10-16 holdout file has 41 rows matching this parent under the 24 state permutations that fix A and B. Of those 41 rows, 40 have one unassigned transition and one has two.

At upstream commit `google-deepmind/cryptids@d1d231afe3a5f6310ac9f956d5687b5a45d7a13d`, the `BusyBeaver/BB6/Halt` and `BusyBeaver/BB6/NonHalt` tree contains 212 Lean modules. An exact table comparison over all 24 A/B-fixing permutations finds seven one-hole source matches among the 41 Raw140 holdouts. Five are the new November 26 batch already listed in `manifest.json`; two were already present in the upstream tree and were not in that 21-proof batch.

The comparison is finite metadata routing. It is not a proof that Raw140 is covered, nor a source-acceptance claim for the two new local bridges below.

## Seven matching holdouts

| Archived holdout (--- is unassigned) | Upstream source completion | Batch / local leaf |
|---|---|---|
| `1RB0LE_1RC0LB_1RD0RC_1LA1RC_---1LF_1LB1LD` | `1RB0LE_1RC0LB_1RD0RC_1LA1RC_HHH1LF_1LB1LD` | Nov 26 / n4, Pair1 |
| `1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB` | `1RB0LE_1RCHHH_1RD1RE_1LA0RF_0RC0LA_0LC0RB` | Nov 26 / n5, Pair1 |
| `1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC` | `1RB0RA_1RC0RD_1RD0LC_1LE1RA_HHH1LF_1RB0LC` | Nov 26 / n8, Pair2 |
| `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---` | `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RDHHH` | Nov 26 / n12, Pair2 |
| `1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA` | `1RB1LF_1RC1RB_1RD0RB_0LE0LF_HHH1LD_0LE1LA` | Nov 26 / n16, Pair3 |
| `1RB0LC_1RC0RA_1RD0RF_0LE---_1LB1LA_1LD1RA` | `1RB0LC_1RC0RA_1RD0RF_0LEHHH_1LB1LA_1LD1RA` | Pre-existing / n19, Pair10 |
| `1RB1LA_1RC0LE_1RD0LF_0LA0RD_1LC0LE_---0RE` | `1RB1LA_1RC0LE_1RD0LF_0LA0RD_1LC0LE_HHH0RE` | Pre-existing / n20, Pair10 |

The two pre-existing modules are both in the NonHalt directory and expose `is_not_halt : IsNotHalt target`:

- F262: `BusyBeaver/BB6/NonHalt/M_1RB0LC_1RC0RA_1RD0RF_0LEHHH_1LB1LA_1LD1RA.lean`, blob `b1b2f3c5aaee2266a514a8078f1084bcf6749899`.
- F068: `BusyBeaver/BB6/NonHalt/M_1RB1LA_1RC0LE_1RD0LF_0LA0RD_1LC0LE_HHH0RE.lean`, blob `6481b36171ed31919fcd6bd9e4ec985f5980eabe`.

Both are pinned by the upstream commit above. Their exact first-use schedules are already in `im-results/agent8-cryptids-tnf-paths/bulk-manifest.tsv`:

- F262: `1:2,2:4,3:6,4:9,5:1,6:5,7:10,9:8,16:3,59:11`.
- F068: `1:2,2:4,3:6,4:1,8:3,9:9,10:8,12:7,71:5,72:11`.

## Local bridge and exact scope

`Nov26Pair10.lean` gives independent literal table equalities, transfers both upstream nonhalting theorems through the existing `CryptidsTapeAdapter`, and constructs the two 25-completion `NeverHalts` leaf Covers.

`Nov26Pair10Weighted.lean` additionally checks the two first-hole schedules, constructs arbitrary-bound `WeightedTNFCertificate` leaves, and proves each leaf is an explicit sequence of eight refinements of the same Raw140 parent. The corresponding dependency manifest is `raw140-pair10-weighted-dependencies.txt`.

Pair10 is pending source CI. Until its exact pinned build passes, n19/n20 remain drafts, not accepted local proofs.

Each one-hole leaf covers 25 completions. The seven listed leaves are only a small subset of the (25^9) completions of Raw140; no Raw140 parent Cover, global count reduction, or BB(6) upper bound follows.
