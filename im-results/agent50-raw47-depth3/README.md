# Raw47 depth-three coverage research

Parent `1RB---_1RC---_0RD---_1LD0RC_------_------`; fixed depth-three roster of 1,212 cylinders, SHA256 `4ae501c6ae90d482f77d8ba65b060717112e402571f887c20fdcd4c4b0bce41d`. The 23 initially difficult low-open parents now have exact weighted coverage proofs: 30 hard leaves discharged by 23 pumping recurrences, six binary counters, and one two-parameter recurrence. Lean source and replay instructions are in PumpCertificates.md and CounterCertificates.md; full parent-cover checks passed in runs [45939716326](https://github.com/FlareZ123/bb6/actions/runs/45939716326) and [45940530291](https://github.com/FlareZ123/bb6/actions/runs/45940530291). These are local Raw47 bounds, not a complete Raw47 cover.

The broader cap-10,000 scan has 45,817 open leaves. FAR through five states closes 43,659; n-grams of widths 2–10 close 1,498 (544 overlap). Adding the 30 hard-leaf theorems leaves 1,192 candidates, across 382 depth-three parents. The 674 pure FAR/cycle-complete parents are undergoing exact eight-shard source checking in [45940910607](https://github.com/FlareZ123/bb6/actions/runs/45940910607); no acceptance claim is made before success. `generate_broad_far.py` replays the frozen parent mask and bank.

## Historical experiments

The verified depth-2 Raw47 cut leaves 114 five-hole residuals, none certified by FAR through six states. This experiment increases the local split depth from 2 to 3 while keeping the same 1,000-step simulation cap and 32-frame cycle lookback. It then runs the FAR5 bank over every resulting open residual.

Reproduce with `.github/workflows/agent50-raw47-depth3.yml` or `bash im-results/agent50-raw47-depth3/run_depth3.sh [output-directory]`.

The purpose is to expose one more undefined transition per surviving branch. Open leaves may therefore have four or five holes depending on whether a branch reaches the simulation cap before the next split. The output records the exact tree, open list, FAR5 candidates, and hole-count distribution.

This is intermediate computational evidence. A candidate bank is not a proof until converted into Lean FAR certificates and checked; a deeper tree does not by itself reduce the global Canonical64 obligation count.
## FAR6 preloader correction

The first FAR6 attempt was invalid: the C++ preloader expects one bare code token per line, but the initial runner passed the FAR5 `id code` output. It therefore parsed IDs as automaton codes and falsely reported all 1212 leaves solved in 0.00 seconds. Those files are explicitly preserved with an `-invalid` suffix. The corrected runner extracts only the second column of the FAR5 bank, validates the ten bare codes, and reruns FAR6. Only the corrected run may be cited.


The prior `raw47-depth3-far6.txt` is invalid (contains numeric IDs treated as codes). Do not use it as evidence.
