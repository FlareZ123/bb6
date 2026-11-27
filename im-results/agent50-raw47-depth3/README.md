# Raw47 depth-three coverage research

Parent `1RB---_1RC---_0RD---_1LD0RC_------_------`.

## Accepted exact quotient cut

**483 open depth-three cylinders at weighted bound 10,006.** The original depth-three tree has 126 first-hole splits, 1,567 cycle closures, 120 state-introduction aliases, and 1,212 distinct canonical residuals. The exact tree cut at weighted bound 84 and its count are accepted by Lean. The current checked consumer removes 729 residual cylinders: 674 pure FAR, 23 original pump/counter, 30 mixed FAR/run-graph pilot parents, and two carry-assisted mixed parents.

`BB6.Agent50Raw47Accepted729.local_sound` establishes that every machine quotient-compatible with the authentic Raw47 parent either satisfies `WeightedBound 10006 m` or is quotient-compatible with a member of the exact remaining roster. The kernel checks `remaining_count` (483), `closed_count` (729), and `keys_eq`; the workflow accepts only standard axioms for all four theorems. This is a partial exact coverage theorem, not a complete Raw47 Cover or a global Canonical57 removal.

- Current accepted composition: [run 45970355702](https://github.com/FlareZ123/bb6/actions/runs/45970355702), artifact `raw47-accepted729` [15184388031](https://github.com/FlareZ123/bb6/actions/runs/45970355702/artifacts/15184388031), SHA256 `1f6262db6e7051d1206c34bd3e8ac9e6bbcb45a44e95073071e35b543cbb0ee8`. Base accepted702: run 45969201649, artifact15184208252; base accepted678: run 45968079265, artifact15183319030.
- Exact roster SHA256 `4ae501c6ae90d482f77d8ba65b060717112e402571f887c20fdcd4c4b0bce41d`. `FastKey.lean` proves injectivity of the twelve-slot base-26 code, with balanced key lookup and exact kernel-computed remainder. The generator does not assume the roster order equals Lean enumeration order.
- The initial accepted108, accepted120, and accepted168 stages were runs 45952099904, 45953219227, and 45953824240. The 17 pump and six counter parent covers were accepted in runs 45939716326 and 45940530291; see PumpCertificates.md and CounterCertificates.md.
- The frozen 674-parent FAR bank is fully accepted via shard 1 (85 parents; 45940910607), the three early 12-parent batches (45952295374, 45952979794, 45952990815), and 45 successful sweep batches covering 529 additional distinct parents (45953448124). The five graph parents (8,23,37,50,55) were accepted by 45954021548.

## Remaining proof edges

The pure-FAR bank and complete 30-parent run-graph pilot are consumed in accepted729. The other 25 pilot parents passed runs 45968751737, 45968758454, 45968764972, 45968770850, 45968777904. Carry-assisted parents 841 and 1062 passed 45969042229 and are also consumed. Agent12's parent174 passed 45970441302; not yet consumed. The interrupted ten-parent graph pilot is retried as size-two shards in 45970362016; 50 new parents are queued in size-five shards in 45970060034. Inspect only exact new successful artifacts. `PartialPrefixAudit.lean`, `QuotientRefinement.lean`, and `SplitMixedPrefix.lean` are locally kernel-checked with standard axioms. The mixed generator exports exact unresolved key sets and recursively shards large trees. Do not rerun pure-FAR or the accepted pilot.

The cap-10,000 scan produced 45,817 open leaves. FAR through five states closes 43,659 candidates; n-grams of widths 2–10 close 1,498 (544 overlap). Adding the original 30 hard-leaf theorems leaves 1,192 candidate leaves across 382 depth-three parents. Agent12's run-graph discovery and Agent2's carry proofs provide further witnesses; only exact parent audits and accepted composition reduce the checked roster. Do not rerun discovery assigned to those agents. `SplitPrefix.lean` and `shard_prefix.py` supply an optional bounded-memory strategy for oversized trees.

## Historical experiments

The verified depth-2 Raw47 cut leaves 114 five-hole residuals, none certified by FAR through six states. This experiment increases the local split depth from 2 to 3 while keeping the same 1,000-step simulation cap and 32-frame cycle lookback. It then runs the FAR5 bank over every resulting open residual.

Reproduce with `.github/workflows/agent50-raw47-depth3.yml` or `bash im-results/agent50-raw47-depth3/run_depth3.sh [output-directory]`.

The purpose is to expose one more undefined transition per surviving branch. Open leaves may therefore have four or five holes depending on whether a branch reaches the simulation cap before the next split. The output records the exact tree, open list, FAR5 candidates, and hole-count distribution.

This is intermediate computational evidence. A candidate bank is not a proof until converted into Lean FAR certificates and checked; a deeper tree does not by itself reduce the global Canonical64 obligation count.
## FAR6 preloader correction

The first FAR6 attempt was invalid: the C++ preloader expects one bare code token per line, but the initial runner passed the FAR5 `id code` output. It therefore parsed IDs as automaton codes and falsely reported all 1212 leaves solved in 0.00 seconds. Those files are explicitly preserved with an `-invalid` suffix. The corrected runner extracts only the second column of the FAR5 bank, validates the ten bare codes, and reruns FAR6. Only the corrected run may be cited.


The prior `raw47-depth3-far6.txt` is invalid (contains numeric IDs treated as codes). Do not use it as evidence.
