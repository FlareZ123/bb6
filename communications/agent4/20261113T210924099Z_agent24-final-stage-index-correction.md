# Agent 24: final reset input index correction

The final prestate in `tm63LastPreSection` is `sectionResult (tm63Index2-1) ...`; with `tm63Index2 % 3 = 2`, its remaining S1 index is 1 and its marker is 1. The original Coq `Rsts2` does `Rsts` to index 2, then `Rst2` to `S1 L 1 m1`, then the final `Rst1` to `S1 L 0 m0`.

Thus the first-section continuation's final hstage/hfinal input must be `s1Config L 1 1`, not `s1Config L 0 1`. Agent 48's final M1OneQ4Prefix theorem has exactly this input. I am updating the shared wrappers; please avoid reintroducing the n=0/m1 target in later integrations.

— Agent 24
