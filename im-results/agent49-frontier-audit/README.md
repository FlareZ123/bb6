# Agent 49, R001: BB(6) frontier concordance (2026-11-03)

**Intermediate source audit. BB(6) remains open.** This dossier distinguishes historical rooted holdouts from externally reported halting evidence. It does not prove a new machine decision.

## Reproducible DeepMind source crosswalk

The 2026-10-16 [holdout snapshot](../../resources/BB6_holdouts_663_2026-10-16.txt) contains 663 unique rooted RLEs, forming 435 unrooted transition tables per [portfolio ledger](../holdout-family-coverage/README.md). The pinned [DeepMind Hardness.lean](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/Hardness.lean) (blob SHA `8b8f09847448ae1e83df75fb6998ee4e3f948531`) mentions 36 distinct exact six-state RLEs; **35 match the October 16 snapshot**. The one absent RLE, `1RB1LA_0RC1RD_1LC0LA_1LE1RE_0RB0LF_---0LD`, is already described as a solved S1 halter in that DeepMind source. Presence in source is not a halting decision. The [pinned source RLE data](hardness-codes-20261024.txt) and [read-only checker](check_hardness_roots.cjs) reproduce this.

## Five dated external reports of Rocq-confirmed halting

The [October 21–26](https://github.com/Yeyito777/bbchallenge-corpus/blob/32869adbaef967d9e43bc97f1ed13c076558a71d/knowledge/discord/bb6/chat/2026-10-21--2026-10-26.md) and [October 27–29](https://github.com/Yeyito777/bbchallenge-corpus/blob/32869adbaef967d9e43bc97f1ed13c076558a71d/knowledge/discord/bb6/chat/2026-10-27--2026-10-29.md) curated Discord digests report five blank-start halters Rocq-confirmed by mxdys. The digests are *secondary, automatically compiled sources*. Original proof files and kernel checks have **not** been independently inspected during this audit.

| Oct 16 line | RLE | Report | Reported step count |
|---:|---|---|---:|
| 311 | `1RB1RE_1LC0RD_1LD0LD_1RA0LC_0LB0RF_0RA---` | Oct 24, Rocq | 15,074,368,710,199 |
| 584 | `1RB1LD_1RC0RB_0LA1RE_1LA0LB_0RA0RF_---0LC` | Oct 24, Rocq | 28,061,938,903,302 |
| 405 | `1RB1RE_1LC1LE_0RD0LB_1RF1RA_0RC0RE_0RA---` | Oct 27, Rocq | 81,681,887,106,169 (Oct 25 simulation) |
| 368 | `1RB0LC_1LA1RD_1LA0LC_0RE---_0RF1RF_0RA0LB` | Oct 27, Rocq | 62,819,215,114,064 (Oct 25 simulation) |
| 462 | `1RB0RA_1LC0RA_1RB1LD_0LE---_0LF1LF_0LB0RC` | Oct 27, Rocq | not supplied |

The exact canonicalization in [the read-only checker](check_reported_halts.cjs) establishes that the five are **five distinct rooted classes in four unrooted table families**. Lines 368 and 462 have identical canonical transition table `0LB---_0LC1LC_0LD0RE_1LE0RF_1RD1LA_1RD0RF` but different canonical initial states (3 and 5, zero-indexed). A source proof for one does not decide the other. The October 27 claimed new `1RB1LC_1RD0RB_1LA0LB_0LA1RE_0RA0RF_---0LD` is a simple *root-preserving relabeling* of line 584, confirmed by canonical table/start equality. See the [detailed source-graded data](2026-10-reported-halts.json).

Run `node im-results/agent49-frontier-audit/check_hardness_roots.cjs` and `node im-results/agent49-frontier-audit/check_reported_halts.cjs` from repository root. Both read pinned inputs without writing files. The second checker validates the October 16 line numbers, rooted canonical identities, and equivalence distinctions. **Neither checker verifies the original external Rocq proofs or the step counts.**

## Unfinished work and candidates

The R001 baseline reports 623 holdouts (Oct 24) and 608 (Oct 30), but exact raw list bytes for those dates were unavailable from reachable sources here; accessible public wiki HTML was older cached content. No claim is made that the five externally reported halters were removed from either specific roster. Obtain dated originals and SHA-256 hashes, then compute true root-sensitive set differences and identify each removal's independently verified reason.

For subsequent transfer experiments consider DeepMind's historically open **#623 parity-shield root** `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA` (Oct16 line517), its independently different **S4 power-trigger root** `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF` (line547), and the independently October27 explicitly claimed still-open `1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA0LE_0RC---` (line262). Confirm current status before claiming new outcome and coordinate with active external researchers. Consult [original DeepMind equivalences](https://google-deepmind.github.io/cryptids/BusyBeaver/BB6/Equivalences/), whose numerical hazard observations are heuristic.

This is a provenance and candidate-selection result in `im-results/`, with **no change to any proven BB(6) bound**.
