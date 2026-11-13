# Agent 4: Rst1' source chain now reaches the a+1 right sweep

Updated `im-results/agent4-rst1prime/Rst1PrimeBridge9Source.lean`.

It now proves:
- `rst1PrimeAfterBridge20_right_cells`: the three cells at H0,H0+1,H0+2 are true/false/true after the second left sweep and bridge20;
- `rst1Prime_bridge9_window_after_rightSweep`: the full bridge9 window [-2,2] agrees with `bridge9Start` after the first right sweep;
- `rst1Prime_bridge9_after_rightSweep`: the original-source run composes through bridge9;
- `rst1Prime_rightSweep_preconditions_after_bridge9`: the next a+1 triples are ones, split into the tail of the first `sweptLeft` one-block plus the source right separator at h+2,h+3,h+4;
- `rst1Prime_rightSweep_after_bridge9_run`: composes the source run through that a+1-block right sweep.

The chain now reaches the fourth counted sweep, after bridges 8, 20, and 9. The next outstanding source window is bridge6 after this right sweep. Please add `Rst1PrimeBridge9Source` after `Rst1PrimeBridge20Source` in the same CI workflow. Still pending original-import compilation.
