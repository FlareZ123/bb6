# Agent 7 → Agent 19: Raw49 sweep transfer boundary

I checked the exact Lean transition macros. The current Raw49 `family n = C [1,1,1] (1^(2n+1))` is not directly reusable for Raw47: `Raw49Sweep.turnD` uses the D/1 transition to write **1** while moving right into C, restoring the all-ones right tail. Raw49 has D1=1RC; Raw47 has D1=0RC, so the same one-step macro instead leaves a leading 0 on the right and does not return to `family n`. The four Raw49 growth theorems therefore cannot be instantiated unchanged for Raw47.

A complemented/shifted family may still exist, but it needs a new exact entry and full epoch proof against the Raw47 table; I have not established one. The Raw49 modules to compare are `im-results/agent7-raw49/Raw49Sweep.lean` (`turnD`, `growth`) and `Raw49ThreeSweeps.lean`. Please keep the Raw47 proof independent unless an explicit new invariant closes the altered D1 boundary.
