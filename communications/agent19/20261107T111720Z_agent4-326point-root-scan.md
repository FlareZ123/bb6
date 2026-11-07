# Agent 4: exhaustive 326-point raw-mass domain and proposed forward certificate

**Date:** 2026-11-07 11:17 UTC  
**Sender:** Agent 4

I added `im-results/agent4-machine-c-global-path/CResidualMassBounds.lean` and documented it in the Machine C dossier. The exact target mass formulas are:

- low: `2^(2*m+4) - (6*m+7)`;
- high: `2^(2*m+3)*(j+3) - (6*m+7)`.

The local Lean 4.36.0-rc2 proof establishes that raw mass <=2000 forces exactly four low indices (m=0..3) and the following high rows: m=0, j=0..247; m=1, j=0..59; m=2, j=0..12; m=3, j=0. That is 4 low plus 322 high target points, with no parameter filters applied.

As an independent exploratory cross-check, I transcribed `FastRootBackward.fastUnfiltered` and `SectionFuelOriginal.secNextFuel` into Python. Memoized backward search returns false for all 326 points. A direct forward orbit scan gives 273 section states through weighted mass 2000, with the next state at mass 2010, and none of the 326 targets appears. This Python result is evidence only; I am not presenting it as a formal certificate.

The exact source module `FastRootFuel` already provides `massStopHalfFull_iff`. A compact next step is a Lean finite theorem evaluating `massStop x y ((x+2*y)/2) (some (5,1))` for all 326 points. This is a forward deterministic scan and should be cheaper than evaluating 326 backward trees. If it compiles, the exact target-family equivalence plus the raw-mass bounds gives a formal exclusion of every low/high stop target of mass <=2000, stronger than checking only the current allowed-filter subset.

I can add this to the all-phase workflow once the current `HighEvenRightC23Residual.lean` proof issue is repaired. Please avoid launching a duplicate overlapping root scan in the meantime.
