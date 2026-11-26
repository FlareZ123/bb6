# Raw112 targeted recovery retry

This is an intermediate recovery plan for the Raw112 parent Cover, not an accepted mathematical result.

## Retained evidence

- Original producer run **45751911115** at source revision `17263f8415b7ad1aa83aa08c7fb8254aa6de5507` retained five successful 3-branch shards: groups `0,2,3,6,7`, covering 15 of the 24 branch roots.
- Recovery run **45787320400** at revision `87917d7b1393c9552bf08987c0ed2862538f3f50` produced nine successful artifacts: `r09,r12,r13,r17,r20,r21,r01b,r05b,r05c`.
- Three recovery cuts failed and are the only work to repeat:
  - `r01a`: `Raw112Kid01_01.lean:1542` hit `maxRecDepth = 100000`; retry that one generated module at 300,000 and split the other eleven modules into two smaller groups.
  - `r04`: compiling the 24-kid branch was interrupted with runner exit 143; compile the 24 kid modules in three groups of eight, then compile the branch aggregator after union.
  - `r05a`: logs were unavailable (HTTP 404); retry its eight kid modules in two groups of four.
- The other nine recovery artifacts are retained in GitHub Actions and must not be recomputed.

## Provenance compatibility

The 22 tracked provenance-input blobs used by the Raw112 shard manifests were compared at the original producer revision, the prior recovery revision, and main at `ab650726a979bad627edaf8c69f975ce31b37d30`; all are identical. The strict `merge_shards.py` checks remain enabled for source paths, source hashes, import graphs, compiler identity, object hashes, module identity, and provenance inputs. `allow_mixed_revisions` only permits the three recorded producer revisions; it does not bypass any identity check.

## Retry layout

1. Merge the five original successful artifacts and nine prior recovery artifacts into a strict partial precompiled union (49 root modules).
2. Compile only eight new cuts against that union:
   - `r01a-rest0`, `r01a-rest1`, `r01a-deep`;
   - `r04a`, `r04b`, `r04c`;
   - `r05a0`, `r05a1`.
3. Merge all 22 artifact groups (93 root modules), compile the three missing branch aggregators (`Raw112Branch01`, `Raw112Branch04`, `Raw112Branch05`), then compile `Raw112Data` and `Raw112ClosedCover`.
4. Audit `BB6.Agent47Raw112.parent_cover` at weighted bound 100,000 with the standard source axiom gate.

The deep-root retry changes only the elaborator's `maxRecDepth` option. The generated theorem statement and proof term are unchanged. The patched source is preserved beside its object and recorded in the final manifest.

## Exact parent

`1RB---_1RC---_0RD---_1LD1RE_---1LC_------`

Do not report Raw112 as closed until the final parent artifact, full 24-branch union, source manifest, dependency reuse checks, and axiom audit all pass.
