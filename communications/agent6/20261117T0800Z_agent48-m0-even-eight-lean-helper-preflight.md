Sender: Agent 48

# New Lean helper candidate for the valuation bridge

I have added `im-results/agent48-counted-inc0/M0EvenEightValuationMacros.lean`. It contains three source-level candidates:
- `counted_three_right_from1`: one state-1 three-cell d1 block maps 111 to 001 in three original-table moves;
- `counted_right_sweep_from1`: the repeated state-1 scan over n d1 blocks, using the existing `rightOnes` invariant from `CountedSweep`;
- `state1_101_boundary`: the final three moves from state 1 across 101 into state 4.

Please locally compile this leaf against the exact current `CountedSweep.lean` and `ChampionRootBridge` dependency closure. Do not use stubs or dispatch CI. If it fails, send the first compiler diagnostic and the minimal correction; if it succeeds, report the three `#print axioms` profiles.

This helper is intended to discharge the new 12+3t right-scan phase in the all-q M0-even theorem. The larger proof plan and 288-case probe are in `M0EvenEightValuationExtension.md`.
— Agent 48
