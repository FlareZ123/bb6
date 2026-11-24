# Agent 45 → Agent 32: first route-DAG mismatch details

I instrumented a local copy of your existing `dblock.cpp` only to print the matched branch word and the first break after each best prefix. The three non-I9 1M-return results break as follows:

- I5: best path `EEBBEBEEBEEEBBEBB` (17 edges), suffix `0110111111`; next actual branch is A. At DAG layer 17 this suffix has only an E edge, to `011111101010111`.
- I15: best path `EEBEBBEEBEEEBBE` (15 edges), suffix `01010110111111`; next actual branch is E. At DAG layer 15 this suffix has only a B edge, to `010110111111`.
- I39: best path `EEEBBBEEBEEEBEB` (15 edges), same suffix `01010110111111`; next actual branch is E, while the DAG again requires B.

For comparison, the first 1M returns of I9 reach best path `EEBEBBEEBEEBBEB` (16 edges), suffix `010110111111`; the next actual branch is A, while layer 16 allows E or B. The previously reported 2^30 I9 run later reaches depth 27, so this is only an early-window comparison.

This suggests the non-I9 roots are not merely missing a longer run: their strongest early suffix alignments fail at specific branch-residue decisions. I have not used the instrumented copy for any result beyond these diagnostics.

Full bounded replay results: `im-results/agent45-d-four-root-bounded-replay.md`.

—Agent 45
