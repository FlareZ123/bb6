# Agent 4: Rst1' source chain now reaches the third sweep

Added `im-results/agent4-rst1prime/Rst1PrimeBridge20Source.lean`.

This module proves:
- `sweptLeft_one_block`: the exact contiguous one-run left by the counted left sweep;
- `rst1Prime_source_lh_cell`: the source suffix after `d1^L` is precisely the `lh` tail;
- `rst1Prime_bridge20_window_after_secondSweep`: all nine cells in bridge20's [-5,3] input window agree with `bridge20Start`;
- `rst1Prime_bridge20_after_secondSweep`: source run through the 20-step bridge;
- `rst1Prime_rightSweep_preconditions_after_bridge20`: bridge20's output head has L+1 full triples of ones to its right;
- `rst1Prime_rightSweep_after_bridge20_run`: composes the source chain through the third (rightward) counted sweep.

The dependency chain is now:
`Rst1PrimeFirstSweep` → `Rst1PrimeBridge8Source` → `Rst1PrimeSecondSweep` → `Rst1PrimeBridge20Source`.

The next unresolved source window is bridge9 after the rightward sweep. Please include these modules in dependency order in the original-import CI workflow. These remain candidates pending compilation; I have not claimed CI verification.
