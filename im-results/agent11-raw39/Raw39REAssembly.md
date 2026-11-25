# Raw39 A1 = 0RE exhaustive child certificate candidate

Literal child `1RB0RE_1RC---_0RD---_1LD0RA_------_------`. Target: `WeightedBound 944` for every compatible completion. **Original-source assembly pending; this is not an accepted cylinder bound.**

Blank-start first undefined query: E/1 after seven live moves. Local reproduction of the pinned tree: 11,593 splits, 214,394 cycles, 49,472 last-hole leaves, 2,774 open leaves. Completion mass 25^6 = 244,140,625. Open SHA256 `63b7913b9cf51527a9c82409266cafe2a9b39e391df1e29b2f3c5f16fbf01c97`; tree SHA256 `bd71ab510b39d2eb9ff18083f8079d8270cc3c9dcad206fa9c21f12e6fefd058`. Maximum enumerated score 944 at `1RB0RE_1RC0LF_0RD0RA_1LD0RA_HHH1LF_1LA1LB` (943 live moves plus final query).

The candidate assigns 64 affine pumps, nine recursive counters, one stack grammar (468) and one source-accepted four-phase cycle (2172, CI 45657974851), i.e. 75 symbolic leaves; 2,699 remaining FAR leaves must pass the original checker. The generator asserts disjointness, exact structural table matches, pinned tree statistics, and FAR mask validation. It does not establish coverage without Lean.

The existing manual workflow agent11-raw39-more.yml now accepts 0RE. Seven groups partition all 24 E/1 children by tree size (37,885–42,625 nodes). The final audit retains 14 other ordinary first-hole obligations of Raw39, besides nine cycle-closed siblings. No global frontier reduction follows yet. Lean 4.36.0-rc2 runs locally, but local GitHub DNS fails, preventing direct original dependency checkout. The connector-supplied enumerator was reproduced locally; the existing CI is the exact-source diagnostic.
