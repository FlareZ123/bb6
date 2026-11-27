# Raw47 depth-three coverage research

Parent `1RB---_1RC---_0RD---_1LD0RC_------_------`.

## Accepted exact quotient cut

**446 open depth-three cylinders at weighted bound 10,006.** The original depth-three tree has 126 first-hole splits, 1,567 cycle closures, 120 state-introduction aliases, and 1,212 distinct canonical residuals. The exact tree cut at weighted bound 84 and its count are accepted by Lean. The current checked consumer removes 766 residual cylinders, adding 37 exact mixed graph/carry parent certificates to accepted729.

`BB6.Agent50Raw47Accepted766.local_sound` establishes that every machine quotient-compatible with the authentic Raw47 parent either satisfies `WeightedBound 10006 m` or is quotient-compatible with a member of the exact remaining roster. The kernel checks `remaining_count` (446), `closed_count` (766), and `keys_eq`; the workflow accepts only standard axioms for all four theorems. This is a partial exact coverage theorem, not a complete Raw47 Cover or a global Canonical57 removal.

- Current accepted composition: [run 46030287702](https://github.com/FlareZ123/bb6/actions/runs/46030287702), artifact 15214337347, digest `sha256:84681ed090b0cf582a81958c9fd8592e92d5210291282415a8ba56584fa65bd0`.
- Previous accepted composition: [run 45970355702](https://github.com/FlareZ123/bb6/actions/runs/45970355702), artifact `raw47-accepted729` [15184388031](https://github.com/FlareZ123/bb6/actions/runs/45970355702/artifacts/15184388031), SHA256 `1f6262db6e7051d1206c34bd3e8ac9e6bbcb45a44e95073071e35b543cbb0ee8`. Base accepted702: run 45969201649, artifact15184208252; base accepted678: run 45968079265, artifact15183319030.
- Exact roster SHA256 `4ae501c6ae90d482f77d8ba65b060717112e402571f887c20fdcd4c4b0bce41d`. `FastKey.lean` proves injectivity of the twelve-slot base-26 code, with balanced key lookup and exact kernel-computed remainder. The generator does not assume the roster order equals Lean enumeration order.
- The initial accepted108, accepted120, and accepted168 stages were runs 45952099904, 45953219227, and 45953824240. The 17 pump and six counter parent covers were accepted in runs 45939716326 and 45940530291; see PumpCertificates.md and CounterCertificates.md.
- The frozen 674-parent FAR bank is fully accepted via shard 1 (85 parents; 45940910607), the three early 12-parent batches (45952295374, 45952979794, 45952990815), and 45 successful sweep batches covering 529 additional distinct parents (45953448124). The five graph parents (8,23,37,50,55) were accepted by 45954021548.

## Remaining proof edges

The 37 newly consumed IDs are 59,62,63,64,65,67,73,74,75,78,81,82,85,88,89,90,91,92,93,94,96,101,104,106,111,112,125,158,162,165,166,167,168,169,174,175,179 (runs 45970441302, 45970362016, 45970060034). The successful size-two sweep 45972740955 and individual runs 45971938822 and 45971469291 yield another 41 distinct full G parents, dispatched for composition into accepted807. Their completion is not yet claimed. The exact partial U61 roster has one leaf, table `1RB1LA_1RC0LF_0RD0LE_1LD0RC_0LA0RB_---1LB`, key 25578468639170103. Independent finite simulation reaches its only undefined transition F0 after 143975 moves. The candidate weighted bound 143977 requires a checked trace; it cannot enter a 10006-bound cut. `PartialPrefixAudit.lean`, `QuotientRefinement.lean`, and `SplitMixedPrefix.lean` are locally kernel-checked with standard axioms. Do not rerun accepted parents.

The cap-10,000 scan produced 45,817 open leaves. FAR through five states closes 43,659 candidates; n-grams of widths 2–10 close 1,498 (544 overlap). Adding the original 30 hard-leaf theorems leaves 1,192 candidate leaves across 382 depth-three parents. Agent12's run-graph discovery and Agent2's carry proofs provide further witnesses; only exact parent audits and accepted composition reduce the checked roster. Do not rerun discovery assigned to those agents. `SplitPrefix.lean` and `shard_prefix.py` supply an optional bounded-memory strategy for oversized trees.

## Historical experiments

The verified depth-2 Raw47 cut leaves 114 five-hole residuals, none certified by FAR through six states. This experiment increases the local split depth from 2 to 3 while keeping the same 1,000-step simulation cap and 32-frame cycle lookback. It then runs the FAR5 bank over every resulting open residual.

Reproduce with `.github/workflows/agent50-raw47-depth3.yml` or `bash im-results/agent50-raw47-depth3/run_depth3.sh [output-directory]`.

The purpose is to expose one more undefined transition per surviving branch. Open leaves may therefore have four or five holes depending on whether a branch reaches the simulation cap before the next split. The output records the exact tree, open list, FAR5 candidates, and hole-count distribution.

This is intermediate computational evidence. A candidate bank is not a proof until converted into Lean FAR certificates and checked; a deeper tree does not by itself reduce the global Canonical64 obligation count.
## FAR6 preloader correction

The first FAR6 attempt was invalid: the C++ preloader expects one bare code token per line, but the initial runner passed the FAR5 `id code` output. It therefore parsed IDs as automaton codes and falsely reported all 1212 leaves solved in 0.00 seconds. Those files are explicitly preserved with an `-invalid` suffix. The corrected runner extracts only the second column of the FAR5 bank, validates the ten bare codes, and reruns FAR6. Only the corrected run may be cited.


The prior `raw47-depth3-far6.txt` is invalid (contains numeric IDs treated as codes). Do not use it as evidence.
