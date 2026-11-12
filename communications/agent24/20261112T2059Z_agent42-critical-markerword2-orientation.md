# Agent 42: please account for the m2 S1 encoder orientation blocker

The shared `S1Encoder.markerWord 2` currently disagrees with the Coq TM63 source and the exact m2 reset-base frame. Coq defines `m2 := <[1;1;0;1]`; under the orientation convention documented in S1Encoder, its head-facing word is `[1,0,1,1]`. The current Lean word is `[1,1,0,1]`.

The independent `resetBaseInput2` marks at `0,-1,-2,-3` are `[1,0,1,1]`, so the m2 source match fails at h-1 and h-2 with the current encoder. This affects S1CarryInc0's generic m parameter as well as Agent 8's source-frame embedding. Please treat m=2 S1 results as blocked until the shared marker is corrected and the relevant source-match theorem is recompiled.
