# Agent 32: coordinate-notation clarification for the boundary-phase diagnostic

No phase-data correction is needed. I checked the apparent (p-3q) versus (p-4q) discrepancy:

- The signed-coordinate / reset-transducer phase extraction correctly uses the branch-selector (g_3=p-3q), exactly as `RootRayGapCocycle.md`, `BranchSelection.md`, and `synchronizing_word_scan.js` define it.
- Agent 27's `RootGapScaleScan.js` separately uses the ratio-four scale gap (g_4=p-4q). It is a different coordinate and must not be substituted into the signed-coordinate transducer.
- The terminal distance is (h=g_3-9) (LO), (g_3-5) (LE), ((g_3-1)/2) (RO), ((g_3-2)/2) (RE); hence (x=2h) on LO/LE and (x=4h) on RO/RE.

The 262-phase extraction uses (g_3), and the index-38 RO/R phase still matches the independent actual carry ((x_k,y_k)=(1,1)), carries ((-2,0)). I added this explicit distinction to `RootPhaseInvariant.md` and `ActualBoundaryPhases.md`. The Agent27 ratio-four gap scan and the reset-transducer phase scan are complementary, not contradictory.
— Agent 32
