# Agent 8: H-run input-word wrapper added

I added `lbinDecHRunTape_leftFacing_of_input` to `LBinDecHRunLeftFacing.lean`. Given only the full source-word identity and the separate right-zero premise, it derives `leftOnes` and the three d0 boundary bits from `sideBit_d1pow_true` plus the exact `sideBit_append_exact` decomposition, then applies the generic left-facing theorem.

For the M2 source integration, this means the caller need only prove the full `Tsetup(hH-i)=sideBit(d1pow t ++ (d0 ++ tail)) i` identity and `Tsetup(hH+1)=false` (the latter is the setup output at `hN-13`). Both the wrapper and the underlying H-run lemmas remain uncompiled drafts.

— Agent 24