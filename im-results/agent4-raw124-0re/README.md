# Raw124 F1=0RE source-audit recovery

**Status: complete source-accepted F1=0RE Cover.** The sparse-FAR subdivision recovery passed in [run 45884922679](https://github.com/FlareZ123/bb6/actions/runs/45884922679) at revision `09d6f56a73dc2183c840f92febf7d628d338ec01`. The exact table is `1RB---_1RC---_0RD---_1LD1RE_---1LF_---0RE`. Lean 4.36.0-rc2 proves `BB6.Agent2Raw124B0RE.bound_all : ∀ m, compatible pBranch m → WeightedBound 2473 m`, and the complete root `checkRoot` succeeds. Both report only `propext`, `Classical.choice`, and `Quot.sound`.

The self-contained [proof artifact 15149067775](https://github.com/FlareZ123/bb6/actions/runs/45884922679/artifacts/15149067775) has SHA-256 `f89ca10db12662221fb37728d7c266d8bc2fdb54911085faebffa689ea2fbcbe`. It contains 174 project .olean objects, the original source pin, stable source hashes, repair/optimization manifests and final axiom log. The 24 F0 ordinary choices and the F0 first-query halt are all covered. No new candidate search was needed.

## Pinned evidence

- Original bundle-sharded run: [45842536675](https://github.com/FlareZ123/bb6/actions/runs/45842536675).
- Exact source revision: `3a265e67cdf4d5a75e41ffa48dade25e1dfade82`.
- Common artifact: `raw124-0RE-common`, artifact ID `15130435830`, SHA-256 `a31bfec4aa195c0ed171f0185d5c8baae4c194eb16ba6125031a46b690411245`.
- Five of six original kid-shard jobs succeeded. The K04–K07 shard was terminated by runner shutdown (exit 143), with no Lean theorem diagnostic.
- Repair run [45855732321](https://github.com/FlareZ123/bb6/actions/runs/45855732321) successfully compiled K06–K07 (artifact `15134618909`), but its K04–K05 job was shut down.
- Separate K04 and K05 repair run [45857825189](https://github.com/FlareZ123/bb6/actions/runs/45857825189) again terminated both jobs (IDs `140040743883`, `140040744130`) with exit 143 and no Lean proof diagnostic.

These are infrastructure/compiler-process failures, not counterexamples to the branch theorem.

## Subdivision recovery

`regenerate_subtree.py` reproduces the source revision's original threshold-500 generated files first. It then changes only the recursive Audit-tree factoring threshold to 50 and regenerates the selected kids.

The prepare step requires:

1. the exact source commit to match the original common-artifact run;
2. the original threshold-500 K04/K05 source to be reproducible;
3. the Base, Pumps and Data source hashes to remain unchanged after subdivision;
4. the K04/K05 root `treeKxx` and `checkKxx` theorem statements to remain unchanged;
5. the source input bundle and generated tree hashes to be retained in `SPLIT_MANIFEST.json`.

The purpose is to replace a few large `by decide` subtrees with smaller recursively assembled proofs. The branch data, transition table, witness bundle, weighted bound and root theorem interface are not changed. The final Lean kernel check remains decisive.

The existing manual target in `.github/workflows/agent13-coverage.yml` now has a preparation job that creates the subdivided sources, separate K04/K05 compile jobs, and the original assembly/standard-axiom gate. The five accepted original shards and K06/K07 from run 45855732321 are reused.

- Subdivision rerun: [45874280943](https://github.com/FlareZ123/bb6/actions/runs/45874280943), queued at 2026-11-26T18:14:12Z.
- Input source run: 45842536675.
- Previous repair run: 45855732321.
- Requested repair kids: K04 and K05.

## Successful sparse-FAR recovery

Threshold-50 subdivision alone still produced runner shutdown at K04 in run 45882800387. Agent2's [optimize_wide_kids.py](optimize_wide_kids.py) preserves the exact original partition, substitutes independently proved `.proven` leaves for the 12 wide (64-state) FAR witnesses, and splits each K04/K05 into its 24 immediate subtrees plus head/root modules. The original Audit checks exact literal table equality at every substituted leaf. The new proofs use the original sound `WeakFAR`, `SparseFAR` and `DirectFAR` checker from Agent3, with the same witness transition and mask data, ordinary kernel `decide`, and no oracle. The Base, Pumps, Data sources and root theorem statements are unchanged. K04 uses nine wide witnesses and K05 three.

- Source optimizer commit `5f842aad0712933d9056686a6c63e275114c7295`; workflow integration `09d6f56a73dc2183c840f92febf7d628d338ec01`.
- Accepted source preparation artifact 15147824927; K04 compiled artifact 15149880521; K05 compiled artifact 15148443863.
- The complete root also compiled independently locally against the accepted Raw58 core and the 22 prior kid objects. All twelve DirectFAR witness proofs and both subdivided kid roots passed locally.

## Acceptance criterion

The final assembly job met all of these criteria:

- verifies the original source pin and `RAW124_SOURCE.sha256`;
- verifies the subdivision manifest against the original and new sources;
- has all 24 `Raw124B0REKidKxx.olean` modules;
- compiles `Raw124B0REData.lean`;
- proves both `checkRoot` and `bound_all` with no `sorryAx` or `native_decide`, and only `propext`, `Classical.choice`, and `Quot.sound`.

The successful source audit also checks the optimized module hashes and all stable root statements. Reuse this complete branch artifact; no further rerun of the witness search or the dense checker is needed.

The only remaining Raw124 obligation is F1=0LF/F0=1RC (Agent12). The accepted nested parent theorem is in run 45885246108; integration of this new 0RE Cover into the exact singleton-cut consumer is underway. No Raw124 full parent Cover or global roster subtraction has yet been established.
