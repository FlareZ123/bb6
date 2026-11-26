# Raw47 one-level-deeper cut and FAR5 search

The verified depth-2 Raw47 cut leaves 114 five-hole residuals, none certified by FAR through six states. This experiment increases the local split depth from 2 to 3 while keeping the same 1,000-step simulation cap and 32-frame cycle lookback. It then runs the FAR5 bank over every resulting open residual.

Reproduce with `.github/workflows/agent50-raw47-depth3.yml` or `bash im-results/agent50-raw47-depth3/run_depth3.sh [output-directory]`.

The purpose is to expose one more undefined transition per surviving branch. Open leaves may therefore have four or five holes depending on whether a branch reaches the simulation cap before the next split. The output records the exact tree, open list, FAR5 candidates, and hole-count distribution.

This is intermediate computational evidence. A candidate bank is not a proof until converted into Lean FAR certificates and checked; a deeper tree does not by itself reduce the global Canonical64 obligation count.
## FAR6 preloader correction

The first FAR6 attempt was invalid: the C++ preloader expects one bare code token per line, but the initial runner passed the FAR5 `id code` output. It therefore parsed IDs as automaton codes and falsely reported all 1212 leaves solved in 0.00 seconds. Those files are explicitly preserved with an `-invalid` suffix. The corrected runner extracts only the second column of the FAR5 bank, validates the ten bare codes, and reruns FAR6. Only the corrected run may be cited.

## Follow-up search results

The depth-3 FAR5 search found 10 certificates among 1212 four-hole leaves. The separate depth-2 FAR searches found 0/114 certificates through seven automaton states. The depth-3 FAR6 run is being rerun after correcting a preloader-format bug; the initial invalid output is preserved with an `-invalid` suffix and must not be cited.

The existing Agent48 AutoPump heuristic was also piloted on the 50 longest depth-3 traces (all 2,001 configurations); it found no candidates. This does not rule out other pump constructions or the Agent46 proof family.
