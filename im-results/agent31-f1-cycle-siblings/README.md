# Raw139 F/1 cycle siblings — candidate source certificates

This intermediate package records eight complete cycle siblings discovered by the exact finite first-hole scan for the raw139 champion-compatible parent

`[7,24,11,24,14,21,3,16,12,11,24,24]`.

Each sibling fixes only F/1 and retains the other three holes. The scan's cycle witnesses are encoded as `Audit.cycle` leaves and checked by the original `FastThreeHoleAudit.fastCheck` in `ChampionF1CycleSiblings.lean`.

| F/1 child | code | cycle audit (entry, period, right, boundary) |
|---|---:|---|
| 0RA | 1 | (0, 13, true, -2) |
| 0LB | 4 | (2, 18, false, 2) |
| 1RB | 7 | (2, 20, false, 4) |
| 0LC | 8 | (2, 14, false, 2) |
| 1LC | 10 | (2, 14, false, 2) |
| 1RC | 11 | (2, 16, false, 3) |
| 0LE | 16 | (2, 14, false, 2) |
| 1LE | 18 | (2, 14, false, 2) |

The scan was cross-checked against the existing ZeroLD candidate: it reproduced exactly 9 splits, 117 translated cycles, 54 last-hole leaves, 5 FAR leaves, and 32 open leaves at the published 600-step / width-3 settings. This is a validation of the scan implementation, not a substitute for the Lean audit.

**Status: pending original-source Lean CI.** If accepted, these are complete WeightedBound(6) covers for all compatible completions of their eight exact cylinders. Integration into the current 108-leaf raw139 frontier is separate and must prove exact parent membership and the resulting residual count. No BB(6) upper bound is claimed.
