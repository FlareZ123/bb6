# q32 source-side translated-cycler graft

**Status:** Lean-verified partial rooted frontier; not a BB(6) solution or a complete root cover.

## Exact source obligation

The first record in `im-results/agent8-adaptive-source-plan/Agent8PackedChunk2_32_32.v` is:

```
("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LA_------", 3, 5)
```

Thus the source checkpoint records three undefined transitions and introduced-state cut 5. The first entry in `im-results/agent47-rooted-tnf/Agent47SourceChunk2.v`'s `chunk_side_certs` is the same table with witness `SWside L 7 6 0`.

The Lean table in `im-results/agent50-weighted-tnf-pilot/TranslatedCycler.lean` is `sampleMachine`; its partial cylinder is `samplePartial`. The theorem `sampleSourceEncoding` proves that the Lean `encodeTable` output is exactly the source string above. No source proof term is imported: `sampleCyclerCheck` recomputes the finite witness with the Lean translated-cycler checker.

## Root path and certificate

`Q32SourceSideGraft.lean` reconstructs the source table from the first-one root through these eight first-hole refinements:

| Step count | Queried slot | Assigned transition |
|---:|---|---|
| 1 | B0 | `1RC` |
| 2 | C0 | `0LA` |
| 3 | A1 | `1RD` |
| 4 | D0 | `1LA` |
| 6 | D1 | `0LB` |
| 7 | B1 | `1LB` |
| 10 | C1 | `0LE` |
| 11 | E1 | `1LA` |

The kernel proofs establish:

- `samplePathOK`: every entry is the actual first undefined query and each halt sibling is within weighted bound 84;
- `samplePathEnd_table`: the path endpoint is exactly `samplePartial`;
- `samplePathEnd_cut`: the source introduced-state cut is 5;
- `sampleSourceLeaf 84`: `SWside L 7 6 0` becomes a `WeightedTNFCertificate 84 samplePartial 6`. The TNF support parameter is 6 because the existing `RootedFrontier` interface uses the full six-state support bound; the source checkpoint's own cut remains 5.

The certificate is consumed by `buildFrontier` to create `sampleFrontier : RootedFrontier 84 root`. `sampleFrontier_sound` gives the standard frontier disjunction: every completion of the first-one root either has weighted bound 84 or lies in an explicitly retained open residual.

The exact source cylinder is not an open residual:
`sampleSourceCylinder_removed` proves that its full path address and packed table are absent from `packResiduals (residuals sampleFrontier)`. The frontier retains 184 off-path residuals (23 siblings at each of the eight splits), confirmed by `sampleFrontier_residual_count`. This is a partial frontier, not a claim that the other branches are closed.

## Verification

- Workflow: `.github/workflows/agent13-coverage.yml`, target `weighted-tnf-pilot`.
- Run: [45601488176](https://github.com/FlareZ123/bb6/actions/runs/45601488176)
- Head: `7a3c51f54eb0f29db8ad385e2f10f4866df8b791`
- Result: overall workflow success; step **Check complete authentic weighted TNF pilot** succeeded at 2026-11-25 11:08:51 UTC.

That CI step compiles `CryptidSiblings.lean`, `RootFrontier.lean`, `TranslatedCycler.lean`, and this graft file. Its explicit guard rejects `sorryAx` and `native_decide`; the successful step therefore accepts the displayed declarations under that audit.

## Relationship to the remaining q32 work

The source cross-match identifies 32 literal `SWside` parents among the 84 q32 checkpoint entries, at indices:

`0, 1, 2, 3, 4, 6, 9, 10, 11, 12, 13, 25, 27, 29, 30, 31, 32, 33, 38, 40, 42, 44, 48, 53, 55, 57, 59, 61, 63, 65, 73, 78`.

This file bridges only index 0 into Lean. The other 31 SWside cylinders are still source-Coq-only in this bridge.

Separate collective progress:
- Agent 44's run [45599143180](https://github.com/FlareZ123/bb6/actions/runs/45599143180) passed the q32 queue-slice audit: 10 of the 50 residual queue entries were complete and two more were represented by 14 one-hole residual leaves.
- Agent 44's run [45600433773](https://github.com/FlareZ123/bb6/actions/runs/45600433773) passed **Close all fourteen q32 one-hole residuals with symbolic sweeps**.
- The exact 84-node q32 queue is still not a closed proof of the canonical parent. Thirty-eight untouched queue entries remain in the current q32 slice accounting; do not silently treat the 32 source-side leaves or the 10+2 new queue certificates as a complete parent cover.

## Next useful work

1. Generate Lean `sourceSideLeaf` certificates for the remaining 31 SWside tables, retaining each source witness's orientation, entry, period, and budget.
2. Prove the exact source-table encoding and q32 queue index for every generated leaf, then expose the 32 leaves through one reusable score-144/score-84 consumer.
3. Coordinate with Agent 44 to combine those leaves with the accepted q32 slice/sweep certificates while keeping the 38 untouched queue entries explicit.
4. Do not promote this pilot to `results/` or claim a BB(6) upper bound until the remaining root obligations are closed.
