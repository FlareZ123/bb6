# Exact BB(6) rooted holdout roster differences, 2026-10-16 to 2026-10-30

**R001 intermediate provenance report, Agent 4, 2026-11-03.** This work establishes the precise contents of dated community *holdout lists*, not an independent proof of any machine's halting status. All three are historical community inventories, not exhaustive upper-bound certificates for BB(6). The exact value of BB(6) remains unknown.

## Source integrity and reproducible comparison

| Dated source | Rooted entries | Raw SHA-256 | Original URL |
| --- | ---: | --- | --- |
| 2026-10-16 | 663 | `cfb2540f8101f2f2f20a14f9bc848252e34e45de2920fdd6b257096093844ee9` | [original](https://wiki.bbchallenge.org/w/images/6/69/BB6_holdouts_663.txt) |
| 2026-10-24 | 623 | `5710f98c37dcb26bffbedf1c5c5d3ef01c5387a9db436221995fa0168fcafc39` | [original](https://wiki.bbchallenge.org/w/images/4/4c/BB6_holdouts_623.txt) |
| 2026-10-30 | 608 | `a5229ff6abd03dd30c59784c0d4e1465754991d197878c139951860ddcab556a` | [original](https://wiki.bbchallenge.org/w/images/5/5e/BB6_holdouts_608.txt) |

The October 16 original bytes are mirrored in [resources](../../resources/BB6_holdouts_663_2026-10-16.txt). The October 24 URL appears in the [wiki source revision 9543, October 25](https://github.com/Yeyito777/bbchallenge-corpus/blob/32869adbaef967d9e43bc97f1ed13c076558a71d/knowledge/wiki/pages/Main/Holdouts_lists.wiki), and October 30 appears in the **live** [wiki raw page](https://wiki.bbchallenge.org/wiki/Holdouts_lists?action=raw), with raw source SHA-256 `bf6f8dc2ccfe6558bdb9db34fe33236e4e75df2d9e996163938f57d9614ab2e3` as fetched 2026-11-03.

[Read-only comparison script](../../tools/bb6_dated_roster_diff.py), run with `python tools/bb6_dated_roster_diff.py` from repo root, fetches originals, validates exact twelve transitions per root and uniqueness, strips the **numeric original-census identifier** preceding each Oct30 rooted RLE, and compares the original blank-A-rooted table strings. These numeric identifiers range from 279 to 181655 and appear on all 608 Oct30 lines; they are not part of a machine table. The script does not identify merely isomorphic *unrooted* tables.

[Manual CI 41560920270, full SUCCESS](https://github.com/FlareZ123/bb6/actions/runs/41560920270) fetched and independently compared all three primary raw lists:
- Oct16→Oct24: precisely **40 removed**, **0 added**, **623 identical retained**. Raw removed rows [TSV](removed-663-to-623.tsv).
- Oct24→Oct30: precisely **15 removed**, **0 added**, **608 identical retained**. Raw removed rows [TSV](removed-623-to-608.tsv).
- Oct16→Oct30: precisely **55 removed**, **0 added**, **608 identical retained**.

The final 608 RLEs are a strict *rooted string subset* of the Oct24 623, which is itself a strict subset of Oct16 663. This is a deterministic dated-roster relation; it does not imply all removed machines were proved.

## Source-graded explanatory evidence for the fifteen removals in October 24→30

The dated [October 21–26 Discord digest](https://github.com/Yeyito777/bbchallenge-corpus/blob/32869adbaef967d9e43bc97f1ed13c076558a71d/knowledge/discord/bb6/chat/2026-10-21--2026-10-26.md) reports **five** exact Oct24-list machines as “confirmed halting in Rocq” by mxdys: the original Oct24 rows **288, 359, 499, 545, 592**. The [October 27–29 digest](https://github.com/Yeyito777/bbchallenge-corpus/blob/32869adbaef967d9e43bc97f1ed13c076558a71d/knowledge/discord/bb6/chat/2026-10-27--2026-10-29.md) reports a further **three** Rocq-confirmed halters, Oct24 rows **341, 376, 430**. All **eight** appear exactly among the 15 removed entries. This corroborates a plausible cause of at least eight removals. These digests are secondary summaries of Discord reports; original Rocq proof files and independently executed Rocq kernel certificates have **not** been retrieved here. The wording “Rocq-confirmed” is therefore an **attributed external report**, not a new mathematical proof by this repository.

The same first digest reports **Oct24 row 63**, `1RB0RB_1LC1RF_0RD0LB_0RA1LE_1LD---_0RB0RC`, halting after Bell 298,793,335 accelerated Bell-map applications according to Thomas Reus, with independent simulation confirmation by Dennis. It explicitly says that producing a Rocq proof was a future task at that date. Its [author's simulator and map repository](https://github.com/thomasreus-bb/Halt-found-1RB0RB_1LC1RF_0RD0LB_0RA1LE_1LD---_0RB0RC) may provide a reusable witness, but **the simulated claim alone is not formal certification**. It is also among the fifteen removed.

The remaining **six** removed original Oct24 rows **109, 119, 146, 247, 411, 531** have **no verified cause in this audit**. One external October 14 snapshot explicitly labels row146 as “OPEN”, with a checked symbolic informal nonhalting argument awaiting independent and Rocq verification ([archived status](https://github.com/DennisKoshta/denniskoshta-portfolio/blob/b48bd32fab8b476135d47ffa4e5f9bfb9a80d8c7/public/busy-beaver/machines/1RB1LB_1RC0LA_1RD0RE_1LA0LB_1RF---_1RB1LD/status.json)). That older label **cannot** establish its later October30 status. Other six roots have search hits in historical lists and informal machine collections but no source-checked modern decisions here.

## Critical distinctions and next decisions

- A historical deletion may reflect a new proof, new simulation, newly identified equivalence, changed enumeration normal form, or an error. Do not silently equate “not in a newer list” with an established halting/nonhalting theorem.
- Oct24 rows 288 and 545 retained their exact RLEs through the Oct24 list despite October24 simulations; they were removed only by Oct30. This demonstrates why inference from report dates to exact roster membership is unsafe.
- The five previously audited Oct16 halter reports in [Agent49's R001 report](../agent49-frontier-audit/README.md) are contained among the Oct24→30 deletions, not among the 40 Oct16→24 deletions. Three additional externally Rocq-reported halters and the Bell-map simulation are also in the latter 15.
- Each entry's **designated blank initial A** remains part of its identity. The source numeric index or an unrooted table-family coincidence never proves the equivalence of different blank starts.
- The new exact dated concordance enables the team to prevent accidental resurrection of already removed cases as supposedly still open and to focus source-level independent verification on the six unexplained deletions or the new 608 roster.
- For an academically significant BB(6) result, the next work must independently verify an original rooted proof or decide a previously unclassified root and integrate into a complete, source-authentic coverage argument. This report belongs under `im-results/`, not `results/`.

**Evidence type:** Primary raw source-list comparison (reproduced), secondary reports of formal halts (not independently checked), and attributed simulation/informal proof (unverified). No BB(6) lower bound, universal upper bound or new machine decision.
