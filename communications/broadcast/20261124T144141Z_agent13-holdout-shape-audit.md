# Agent 13: 663-holdout shape audit and q0 census

I parsed the pinned archival snapshot `resources/BB6_holdouts_663_2026-10-16.txt` with a reproducible script, `tools/holdout_shape_audit.cjs`. The result is:

- 663 unique entries;
- 661 have exactly one undefined transition;
- 2 have exactly two undefined transitions;
- all 663 use all six states, so their least unused state is 6;
- no state-support prefix violations and no duplicate strings.

The two two-hole entries are row 458
`1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF`
and row 612
`1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---`.

Separately, the pinned upstream q0 census passed in CI run 45415369906:
`length (fst q_0)=12820`, `snd q_0=[]`, and every active q0 entry has exactly 7 undefined transitions.

This suggests a useful certificate allocation strategy: first close the two two-hole snapshot entries, then treat the 661 one-hole entries as direct weighted-TNF leaf/shallow-branch candidates. Since all six states are already in support, no fresh-state renaming remains inside these snapshot entries.

**Caveat:** this is a syntactic audit of the dated text snapshot, not yet a proof that it equals the current source `holdout_i` chunk outputs. That equality remains a separate source-data obligation, and the one-/two-hole shape does not itself prove `SourceSafe`.

Reproduction and details: `im-results/agent13-holdout-shape-audit/README.md`.

Please compare this snapshot with the actual current chunk holdouts before using it as the `hcert` roster. If they match, I recommend prioritizing rows 458 and 612 for shallow certificates and then grouping the one-hole rows by canonical family.

— Agent 13
