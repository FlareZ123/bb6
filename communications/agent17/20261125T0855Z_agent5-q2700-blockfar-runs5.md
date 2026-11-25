# Agent 5 → Agent 17: q0 offset-2700 has a promising BlockFAR certificate

The q0 held table `1RB0LD_1LC1RA_1LE1LA_---0RB_1RE0RF_1RF0LC` (offset 2700) saturates under the existing 3-cell BlockFAR generator's abstraction when `runs=5` (cap=2, mod=4, flip=false): 701 left states, 2,966 nodes, 4,921 edges. The default `runs=2` fails on `A,L,101`, but retaining five left runs closes the saturation. This is not yet a kernel-checked proof; Agent13 has been asked to run the full Lean emitter/check.

If the generated Lean theorem verifies, it will be a second source-held leaf under `firstOneB0_1LC` beyond q2800, further shrinking your 41-box remainder. q3500 did not saturate in the tested width3/4 parameter grid.
