# Raw47 depth-three coverage research

Parent `1RB---_1RC---_0RD---_1LD0RC_------_------`.

## Accepted exact quotient cut

**1,044 open depth-three cylinders at weighted bound 10,006.** The accepted168 consumer from run 45953824240 extends the accepted120 result below; the later successful sweep and graph exports are not yet consumed into a stronger exact cut. The original depth-three tree has 126 first-hole splits, 1,567 cycle closures, 120 state-introduction aliases, and 1,212 distinct canonical residuals. The exact tree cut at weighted bound 84 and its count are accepted by Lean. 120 residual cylinders are now removed by injective base-26 twelve-slot keys and balanced membership, consuming 97 FAR-only and 23 pump/counter parent-cover theorems.

`BB6.Agent50Raw47Accepted120.local_sound` states for every machine quotient-compatible with the authentic Raw47 parent that either `WeightedBound 10006 m` holds or there exists an entry of `remaining` quotient-compatible with that machine. `remaining_count` proves `remaining.length = 1092`; `closed_count` proves the consumed bank has 120 entries. All depend only on propext, Classical.choice, Quot.sound. This is a partial exact coverage theorem, not a complete Raw47 Cover or a global Canonical57 removal.

- Initial 108 composition source: [512da296](https://github.com/FlareZ123/bb6/commit/512da29611cdd158d414e45fad744bf2118c8641), `Raw47Accepted108.template`, `generate_accepted108.py`, `merge_accepted_artifacts.py`.
- Initial accepted Lean 4.36.0-rc2 [run 45952099904](https://github.com/FlareZ123/bb6/actions/runs/45952099904), [artifact 15177403000](https://github.com/FlareZ123/bb6/actions/runs/45952099904/artifacts/15177403000), SHA256 `ad8c0c0b97ab069910c369fc048fd4831be39c2876c1da2298c49f68a50a7e89`. 197 existing dependency-closed objects reused with zero incompatible entries, two new modules compiled; manifest has 199 modules.
- Current accepted composition: [run 45953219227](https://github.com/FlareZ123/bb6/actions/runs/45953219227), [artifact 15177686849](https://github.com/FlareZ123/bb6/actions/runs/45953219227/artifacts/15177686849), SHA256 `9982e26448e8ccd2d3e61100c9b42269a67ea1852b044fd8ca63ce91b37388c8`. Source [1b678ef](https://github.com/FlareZ123/bb6/commit/1b678ef83c34768df6f044d2136a96ad9eaa7865), `FastKey.lean`, `generate_fast_consumer.py`. The packed key's injectivity and balanced lookup are proved; local composition took 6.09s. Additional 12 covers are from run 45952295374.
- Fixed roster SHA256 `4ae501c6ae90d482f77d8ba65b060717112e402571f887c20fdcd4c4b0bce41d`. The generator's roster ordering is not assumed equal to Lean's enumeration; `tableKey_inj` proves extensional equality and the exact filter count is computed by the kernel.
- Accepted sources: 17 pump and six counter parent covers from [45939716326](https://github.com/FlareZ123/bb6/actions/runs/45939716326) and [45940530291](https://github.com/FlareZ123/bb6/actions/runs/45940530291); see PumpCertificates.md and CounterCertificates.md. FAR shard 1 (85 parents) from [45940910607](https://github.com/FlareZ123/bb6/actions/runs/45940910607), artifact 15173243661. The initial other seven shards failed or were cancelled. Subsequent independent 12-cover batches for shards 0, 3, 4 have accepted (runs 45952295374, 45952979794, 45952990815); the latter two are not yet consumed into the 120-cover composition.

The broader cap-10,000 scan has 45,817 open leaves. FAR through five states closes 43,659; n-grams of widths 2–10 close 1,498 (544 overlap). Adding the 30 hard-leaf theorems leaves 1,192 candidate leaves across 382 depth-three parents. Agent12 is developing run-graph witnesses for the 515 non-pure-FAR/nonhard parents; Agent2 has five exact carry proofs of its hard10 leaves. These are separate from the accepted 120-parent reduction until they are consumed by exact parent audits.

## Next proof edge

The existing manual workflow `.github/workflows/agent50-raw47-depth3-far6-lean.yml` now supports `mode=far-batch` with shard, offset and size, reusing the accepted shard-1 core and the frozen witness bank. Use small nonoverlapping batches for the seven incomplete shards (shard 1 already accepted), then consume accepted parent bounds into the exact quotient filter. This avoids the interrupted 85-parent-per-shard monolithic gate. The completed sweep [45953448124](https://github.com/FlareZ123/bb6/actions/runs/45953448124) exported **45 successful batches covering 529 additional distinct pure-FAR parents**; two 12-parent batches (shard 3 offset 36 and shard 5 offset 48) were interrupted by runner shutdown (exit 143), with no accepted export. The five mixed graph parents (8, 23, 37, 50, 55) passed [45954021548](https://github.com/FlareZ123/bb6/actions/runs/45954021548), artifact 15178262071. An earlier composition [45953824240](https://github.com/FlareZ123/bb6/actions/runs/45953824240) consumed 168 parents (artifact 15177703491), before the sweep finished. Thus the currently accepted exact cut has 1,044 remaining at the same bound; the next complete-batch consumer pins the 45 exports, two earlier 12-parent exports and five graph parents against the accepted120 base. Its expected count is 678 closed / 534 remaining; that stronger cut is **not yet kernel accepted**. Retry only the two interrupted batches in smaller groups. `SplitPrefix.lean` and `shard_prefix.py` offer an optional bounded-memory strategy for oversized trees, tested locally on parent 21 with the original accepted core. Do not repeat accepted batch proofs or rerun graph discovery already assigned to Agent12.
 
## Historical experiments

The verified depth-2 Raw47 cut leaves 114 five-hole residuals, none certified by FAR through six states. This experiment increases the local split depth from 2 to 3 while keeping the same 1,000-step simulation cap and 32-frame cycle lookback. It then runs the FAR5 bank over every resulting open residual.

Reproduce with `.github/workflows/agent50-raw47-depth3.yml` or `bash im-results/agent50-raw47-depth3/run_depth3.sh [output-directory]`.

The purpose is to expose one more undefined transition per surviving branch. Open leaves may therefore have four or five holes depending on whether a branch reaches the simulation cap before the next split. The output records the exact tree, open list, FAR5 candidates, and hole-count distribution.

This is intermediate computational evidence. A candidate bank is not a proof until converted into Lean FAR certificates and checked; a deeper tree does not by itself reduce the global Canonical64 obligation count.
## FAR6 preloader correction

The first FAR6 attempt was invalid: the C++ preloader expects one bare code token per line, but the initial runner passed the FAR5 `id code` output. It therefore parsed IDs as automaton codes and falsely reported all 1212 leaves solved in 0.00 seconds. Those files are explicitly preserved with an `-invalid` suffix. The corrected runner extracts only the second column of the FAR5 bank, validates the ten bare codes, and reruns FAR6. Only the corrected run may be cited.


The prior `raw47-depth3-far6.txt` is invalid (contains numeric IDs treated as codes). Do not use it as evidence.
