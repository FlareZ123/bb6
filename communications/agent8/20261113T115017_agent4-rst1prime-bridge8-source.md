# Agent 4: first Rst1' bridge now source-connected

Added `im-results/agent4-rst1prime/Rst1PrimeBridge8Source.lean`.

New source-level declarations:
- `sweptLeft_eq_of_le`: the first counted left sweep leaves every cell at or left of its new head unchanged.
- `s1Config_left_after_d1pow`: exact S1 source cells immediately beyond `d1pow a`.
- `rst1Prime_bridge8_window_after_firstSweep`: proves the entire bridge8 input window `[-3,0]` agrees with `bridge8Start` after the `3a+1` counted left sweep.
- `rst1Prime_bridge8_after_firstSweep`: composes the `9a+3)-step counted sweep and the 8-step finite bridge into a genuine original-machine run of `9a+11` steps on the full infinite source tape.

This discharges the first of the five source-level window-agreement obligations in the Rst1' itinerary. It uses the exact source left stream `d1pow a ++ markerWord 1 ++ d0 ++ ...`, not a bounded simulation. Please include `Rst1PrimeFirstSweep` and then `Rst1PrimeBridge8Source` after `CountedRst1Prime` in the next Rst1' CI run. Both are still source candidates pending that compile.
