# Shape audit of the 663-machine holdout snapshot

This is a reproducible structural audit of
`resources/BB6_holdouts_663_2026-10-16.txt`, using
`tools/holdout_shape_audit.cjs` and the shared RLE parser in
`tools/holdout_families.cjs`.

Run:

```sh
node tools/holdout_shape_audit.cjs resources/BB6_holdouts_663_2026-10-16.txt
```

## Observed snapshot structure

The file contains 663 unique machine strings:

| Property | Count |
|---|---:|
| Exactly one undefined transition | 661 |
| Exactly two undefined transitions | 2 |
| All six states occur in the support | 663 |
| Least unused state (`fresh`) equals 6 | 663 |
| Non-prefix state-support cases | 0 |
| Duplicate machine strings | 0 |

The two two-hole entries are:

- Row 458: `1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF`
- Row 612: `1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---`

Thus, within this dated snapshot, the unresolved tables are already fully state-supported: 661 require closing one missing transition and two require closing two. There are no remaining fresh-state renamings inside these entries. This makes them natural inputs for direct weighted-TNF leaf or shallow-branch certificates.

## Relation to the source queue

A separate bounded Coq census of the pinned upstream `q_0` succeeded in CI run
[45415369906](https://github.com/FlareZ123/bb6/actions/runs/45415369906):
`length (fst q_0)=12820`, `snd q_0=[]`, and all 12,820 active entries have
`num_undef_trans=7`.

**Important limitation:** the shape audit above is only about the dated text
snapshot. It does not prove that these 663 strings are exactly the union of
the current upstream `holdout_i` chunk outputs. That equality still needs a
source computation or certificate. Likewise, one or two holes do not by
themselves establish a weighted bound; every compatible completion must
still be covered.

The audit is an intermediate research result, not a theorem determining
`BB(6)`.
