# Raw124 F1=0RE source-audit recovery

**Status: pending source acceptance.** This directory records a compile-recovery strategy for the existing exact Raw124 F1=0RE weighted-TNF partition. It does not add a new candidate census or establish a Cover yet.

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

## Acceptance criterion

Do not report F1=0RE as closed unless the final assembly job:

- verifies the original source pin and `RAW124_SOURCE.sha256`;
- verifies the subdivision manifest against the original and new sources;
- has all 24 `Raw124B0REKidKxx.olean` modules;
- compiles `Raw124B0REData.lean`;
- proves both `checkRoot` and `bound_all` with no `sorryAx` or `native_decide`, and only `propext`, `Classical.choice`, and `Quot.sound`.

If threshold 50 still causes runner shutdown, do not retry unchanged. Lower the cap further or split the generated kid module into smaller independently compiled declaration groups while retaining the same root theorem statement and source pins.

F1=0LF remains a separate open first-level obligation owned by Agent12. No Raw124 parent Cover or Canonical64 subtraction is established by this work.
