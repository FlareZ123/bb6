# q32 source-side translated-cycler graft

**Status:** Lean-verified 32-cylinder source-side roster and exact root-residual relation; not a BB(6) solution or a complete canonical-parent cover.

## Exact source obligation

The first record in `im-results/agent8-adaptive-source-plan/Agent8PackedChunk2_32_32.v` is:

```
("1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LA_------", 3, 5)
```

Thus the source checkpoint records three undefined transitions and introduced-state cut 5. The first entry in `im-results/agent47-rooted-tnf/Agent47SourceChunk2.v`'s `chunk_side_certs` is the same table with witness `SWside L 7 6 0`.

The Lean table in `im-results/agent50-weighted-tnf-pilot/TranslatedCycler.lean` is `sampleMachine`; its partial cylinder is `samplePartial`. The theorem `sampleSourceEncoding` proves that the Lean `encodeTable` output is exactly the source string above. No source proof term is imported: `sampleCyclerCheck` recomputes the finite witness with the Lean translated-cycler checker.

## Root path and first certificate

`Q32SourceSideGraft.lean` reconstructs the sample source table from the first-one root through these eight first-hole refinements:

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

## All 32 original SWside certificates in Lean

`Q32SideLeafRoster.lean` translates all 32 `SWside` entries from `Agent47SourceChunk2.v` into Lean `WeightedTNFCertificate 144` leaves. It preserves, for every entry:

- the exact partial-table string and a proof that `encodeTable` returns that string;
- source orientation (`L/R`), entry, period, and budget;
- source queue index and (holes, introduced-state-cut) metadata;
- the finite translated-cycler check, recomputed in Lean rather than importing the Coq proof.

The exact q32 queue indices are:

`0, 1, 2, 3, 4, 6, 9, 10, 11, 12, 13, 25, 27, 29, 30, 31, 32, 33, 38, 40, 42, 44, 48, 53, 55, 57, 59, 61, 63, 65, 73, 78`.

The module includes the 84-row q32 queue export and proves:

- `q32SideData_sourceExact`: all 32 source-side records match the exact queue table and metadata at their stated indices;
- `q32SideLeaves_data_exact`: the certificate roster has exactly the source witness metadata;
- `q32SideLeaves_sound`: every completion of each of the 32 cylinders has weighted bound 144.

### Exact connection to the existing root frontier

The q32 parent is the depth-two branch `B0=1RC, C0=0LA` from the first-one root:

```
1RB---_1RC---_0LA---_------_------_------
```

The module proves:

- `q32Parent_is_rootFrontier_residual`: the packed parent table at address `[1RC, 0LA]` is an exact open residual of Agent 50's existing `rootFrontier`;
- `q32SideLeaves_refine_parent`: a finite Boolean check over all 12 slots confirms that all 32 source-side cylinders fix every transition fixed by this parent;
- `q32SideLeaves_refine_parent_sound`: the Boolean refinement check implies the corresponding proposition `Refines leaf.cylinder q32Parent`.

This is an exact root-fixing subsumption relation, not merely a string similarity. The 32 certificates establish weighted bound 144 on these subcylinders of the existing root residual. They do **not** close the entire parent residual, and because the original `rootFrontier` is at bound 84, these bound-144 leaves do not by themselves close that particular bound-84 frontier.

## Verification

The workflow target is `weighted-tnf-pilot` in `.github/workflows/agent13-coverage.yml`. Its explicit axiom guard rejects `sorryAx` and `native_decide`.

| Run | Result | Scope |
|---|---|---|
| [45601488176](https://github.com/FlareZ123/bb6/actions/runs/45601488176) | Success | Sample source path, certificate, and rooted frontier |
| [45602794545](https://github.com/FlareZ123/bb6/actions/runs/45602794545) | Success | All 32 source-side certificates and exact queue-data mapping |
| [45603623804](https://github.com/FlareZ123/bb6/actions/runs/45603623804) | Success | Exact q32-parent residual membership and all 32 refinement checks |

The latest run's **Check complete authentic weighted TNF pilot** step succeeded at 2026-11-25 11:22:58 UTC. The compiled closure includes `CryptidSiblings.lean`, `RootFrontier.lean`, `TranslatedCycler.lean`, `Q32SourceSideGraft.lean`, and `Q32SideLeafRoster.lean`.

## Relationship to the remaining q32 work

Separate collective progress from Agent 44:

- Run [45599143180](https://github.com/FlareZ123/bb6/actions/runs/45599143180) passed the q32 queue-slice audit: 10 of the 50 residual queue entries were complete and two more were represented by 14 one-hole residual leaves.
- Run [45600433773](https://github.com/FlareZ123/bb6/actions/runs/45600433773) passed **Close all fourteen q32 one-hole residuals with symbolic sweeps**.

The current q32 accounting still has 38 untouched queue entries. The 32 Lean-verified SWside cylinders, the two original source sweep witnesses, and Agent 44's newer 10+2 slice/sweep closures must be combined with the exact queue complement before claiming the canonical parent is closed. Do not silently treat this roster as a complete parent cover.

## Next useful work

1. Integrate the 32 Lean SWside leaves with Agent 44's accepted q32 slice/sweep certificates in one source-queue closure manifest.
2. Keep the 38 untouched queue entries explicit and prioritize closing them or proving a universal complement.
3. Decide whether to lift the root frontier to bound 144 and consume these subcylinders there, rather than conflating the existing bound-84 frontier with bound-144 certificates.
4. Do not promote this pilot to `results/` or claim a BB(6) upper bound until the remaining root obligations are closed.
