# Six unexplained deletions from the October 24 to October 30 BB(6) holdout rosters

**Agent 29, R001 source-grade intermediate report, 2026-11-03.** This documents raw-table relationships and research-source provenance. The report does **not** prove any new machine halting or nonhalting verdict, certify that the October 30 community list is exhaustive, or change a Busy Beaver bound. It belongs in `im-results/`.

## Pinned enumeration and reproducibility

[Agent 4's primary-source concordance](../agent4-dated-roster/README.md) established exact rooted set inclusions: 663 October 16 roots, 623 October 24, and 608 October 30. For reproducibility, the local Oct16 file is [here](../../resources/BB6_holdouts_663_2026-10-16.txt); the Oct24→30 deletions are [here](../agent4-dated-roster/removed-623-to-608.tsv). The external Oct24/Oct30 raw file SHA-256 values in the Agent 4 dossier distinguish dated community snapshots. Roster membership is distinct from a machine outcome.

Run `node tools/agent29_roster_removals.cjs` from repository root. The read-only checker uses the existing [exact six-state canonicalizer](../../tools/holdout_families.cjs) and independently checks a literal table-reflection identity. It validates input counts, all 15 deleted entries, six targeted roots, sibling starts, and table-family groups. [Manual GitHub Actions run 41563487122: SUCCESS](https://github.com/FlareZ123/bb6/actions/runs/41563487122) executed the complete checker on 2026-11-03.

All 15 October24→30 deleted rooted strings represent exactly **10 distinct unrooted transition tables** under state renaming and tape reflection. Their Oct24-line groups are `[63], [109], [119], [146,411], [247], [288,359,499,592], [341,430], [376], [531], [545]`. The six previously unexplained deleted strings represent **five** unrooted tables. This grouping is combinatorial; halting results cannot be transferred across distinct initial states without a proof.

## Exact source and sibling inventory for the six unexplained deleted roots

| October 24 row | Exact rooted machine | October 16 line | Same unrooted-table family in October 16 | Source lead / unresolved question |
| --- | --- | ---: | --- | --- |
| 109 | `1RB0LE_0RC---_1RD0LA_1RE0RF_1LC1RD_1RE1RA` | 121 | only 121 in pinned roster | J. Huang source reports an accelerated halting run, without a separately certified primitive-step witness |
| 119 | `1RB1LB_1RC---_1LD1LF_1LE0LD_0LA1RF_1LC0RE` | 132 | 132 deleted; **505 retained October 30** | Different root on the same table remains listed; reason for deletion of 132 not established |
| 146 | `1RB1LB_1RC0LA_1RD0RE_1LA0LB_1RF---_1RB1LD` | 160 | 160 and 443 both deleted | Original research snapshot gives a symbolic *informal* nonhalting argument for its initial A state |
| 247 | `1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_0RA---` | 267 | only 267 in pinned roster | No original proof or halting witness identified in this audit |
| 411 | `1RB0RC_1LC1RC_1LD0RB_1LA0LE_1LF---_1LC1RA` | 443 | 160 and 443 both deleted | Original research snapshot gives a second symbolic *informal* nonhalting argument for the original table's D start |
| 531 | `1RB1LC_1RC0LE_1RD1RF_1LE0LB_1RF1LB_0RA---` | 570 | only 570 in pinned roster | No original proof or halting witness identified in this audit |

The retained exact sibling for row 119 is Oct16 line **505**, `1RB1RF_1RC0RB_0RD1LF_1LE1RE_1LA---_1RA0LC`. Its initial A state belongs to a different rooted class from deleted row 119. Treat both statuses independently.

### Rows 146 and 411: literal rooted conjugacy and distinct initial states

The transformation sending row 146's states `A→B, B→C, C→D, D→A, E→E, F→F`, **with L/R reflection**, maps **all twelve** row 146 entries exactly to row 411's entries. No symbol complement is involved. Under the inverse mapping, row 411's blank-initial **A** is row 146's initial **D**. Row 146 itself begins at A, so the two roots are **not** simply identical blank-start machines.

The independent [Dennis Koshta machine archive](https://github.com/DennisKoshta/denniskoshta-portfolio/tree/b48bd32fab8b476135d47ffa4e5f9bfb9a80d8c7/public/busy-beaver/machines/1RB1LB_1RC0LA_1RD0RE_1LA0LB_1RF---_1RB1LD) has a [dated status file](https://github.com/DennisKoshta/denniskoshta-portfolio/blob/b48bd32fab8b476135d47ffa4e5f9bfb9a80d8c7/public/busy-beaver/machines/1RB1LB_1RC0LA_1RD0RE_1LA0LB_1RF---_1RB1LD/status.json) (last updated October 14; static site captured October 17). It labels the entire table **OPEN**, `stage=informal_proof`, and explicitly states a common invariant:

```text
INV = {N(Y) : Y >= 22} union {Q(W) : W >= 14}
N(Y) ->+ N(2^18 Y + 32859022)
Q(W) ->+ Q(2^18 W + 34431880)
```

Its attached `proof.md.html` covers both starts: initial A eventually enters N and initial D eventually enters Q after a giant counter phase. The author reports `check_proof.py` assertions passing, but says its engine has **not** been independently checked or formalized in Rocq. This is an attributed *informal* nonhalting argument, not a kernel-checked proof; the October30 roster deletion by itself does not upgrade its status.

### Row 109: original external accelerated halt report, October 15

The exact row109 code occurs at the top of the original [J. Huang analysis notes](https://github.com/jhuang97/turing_machine/blob/91f0b8d915197aab925ba2c1cd2f1879325ab151/notes/bb6_1DCA_like_notes.txt), under `tm =` in all three [higher-level rule definition files](https://github.com/jhuang97/turing_machine/tree/91f0b8d915197aab925ba2c1cd2f1879325ab151/src/definitions), and as `TM_DEF` in [src/bin/bb6_1DCA_like.rs](https://github.com/jhuang97/turing_machine/blob/6aeb2384173cf4c93a9a7c7f418bb9b7b1839b39/src/bin/bb6_1DCA_like.rs). The October 15, 2026 commit `6aeb238` is explicitly titled **“simulate BB(6) 1dCA-like to halting.”**

The author reports a final accelerated state, where `FastLongSim.halted` becomes true, at **6,431,143,049** internal simulator calls, with **2,687,980,000** applied right-end heads and **1,380,279,297** logical digits represented in a compressed tape. These counters **are not standard one-cell TM steps**, so neither is a legitimate BB(6) step score. The source ends with “Need to double check against a simpler simulator to make sure the head sequence is right...”. It contains right-end cache code, finite block macros, and tests for shorter consistency, but no independently reproduced full-run primitive-step certificate retrieved here.

**Best follow-up:** replay the raw-table-to-macro startup, independently verify every visited right-end cache rule and the terminal halt, and obtain a reproducible primitive-step count or certified halting witness. This is a plausible explanation for historical deletion of row109, **not independently established** as the reason.

## Other provenance and decisions

- A root-sensitive comparison against all 89 named pinned Google DeepMind `BusyBeaver/BB6/` and `BusyBeaver/BB6/Accelerations/` Lean machine modules (commit `c86f15861709b76042998c5211c7b2f83991621b`), allowing all state renamings that keep the initial state and both tape orientations, did not find any of these six as a direct named-module match. This is a **limited filename/index comparison** and cannot establish that a proof does not exist elsewhere or under macro/halting equivalence.
- The public [Enan456/bbchallenge-proofs](https://github.com/Enan456/bbchallenge-proofs/blob/72965887b21cfc0310a90c93ec36b09d8b3ee8f6/qgkit/bb6/reprobe_rejects.py) classifies row119 and its retained sibling as **automated orbit-fitter rejects** at bounded budgets. This is not a halting/nonhalting decision; that project's own README says it does not decide machines.
- External [jhuang97's Skelet-1-like list](https://github.com/jhuang97/turing_machine/blob/91f0b8d915197aab925ba2c1cd2f1879325ab151/bb6_Sk1-like.txt) contains row531 among machines sharing a heuristic family; this is taxonomy only, not a theorem.
- For rows 119, 247, 531, no primary formal outcome was identified. For rows 146, 411, full original symbolic proof replay and Rocq/Lean formalization remain open. For row109, independent end-to-end halting verification remains open.

**Scientific outcome:** reproducible corrected research provenance and immediate original-source leads on three of the six deleted rooted cases; **no new proof of any root's status, no novel Busy Beaver bound, and no claim that list membership defines the unsolved frontier**.
