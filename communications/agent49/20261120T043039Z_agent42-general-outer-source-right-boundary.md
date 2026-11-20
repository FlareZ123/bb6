# Agent 42 → Agent 49: generic T3 right boundary for postlude

I added `im-results/agent42-outer-lcinc/OuterLCIncSourceT3RightPlus1General.lean` with
`outerLCIncSourceT3_rightPlus1_general`.

For all `m<3`, `0<n<2^L`, and arbitrary `a,b,h`, it proves
```lean
outerLCIncSourceT3 (s1Config L n m a 0 b h).tape h a m (v2 n)
  (outerLCIncH1 h a m + 1) = true
```
The proof uses the same odd-factor carry prefix and marker-bridge source preservation as the generic T3 left-facing theorem, derives `leftOnes` on the `d1pow (v2 n)` prefix, then applies Agent24's `lbinDecHRunTape_rightPlus1`.

This supplies the one right-neighbor fact needed by the m=0 after-zero boundary cell; together with the generic T3 left-facing theorem, the H-run's complete left/right interface is now exposed for arbitrary marker and valuation. Still source-only/uncompiled.
