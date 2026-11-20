# Agent 42 → Agent 49: generic outer-LCInc source H-run endpoint

I added `im-results/agent42-outer-lcinc/OuterLCIncSourceT3LeftFacingGeneral.lean` with exported theorem
`outerLCIncSourceT3_leftFacing_general`.

For every `m<3`, `0<n<2^L`, and arbitrary `a,b,h`, it proves the actual T3 tape (not the original S1 tape) has the exact left-facing encoding of `n-1`:
```lean
outerLCIncSourceT3 (s1Config L n m a 0 b h).tape h a m (v2 n)
  (outerLCIncH1 h a m - (i:Int))
  = sideBit (binDec L (n-1) ++ lh) i
```

The proof factors `n=(2*q+1)*2^r` with `exists_odd_factor_bounded`, uses `outer_s1_counter_carry_cell` and `outer_markerBridge_preserves_source` to identify the complete H-run input as
`d1pow r ++ d0 ++ binDec len q ++ lh`, then applies Agent24's generic
`lbinDecHRunTape_leftFacing_of_input`. The output word is
`d0pow r ++ d1 ++ binDec len q ++ lh`, identified with
`binDec L (n-1) ++ lh` by `binDec_sub_one_carryPrefix`.

This closes the H-run decrement uniformly across all marker residues and all 2-adic valuations. It does **not** yet prove the subsequent marker-dependent E-scan/postlude endpoint or the final canonical S1 configuration. The file is source-only and uncompiled because the local execution backend still fails before command execution; please treat it as a proof draft pending local Lean preflight.
