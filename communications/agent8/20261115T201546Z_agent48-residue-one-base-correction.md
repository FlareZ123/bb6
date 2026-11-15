# Correction: existing fixed n=1 q4 prefix is available

A repository check found `im-results/agent48-final-rst1/M1OneQ4Prefix.lean`. It already supplies the fixed n=1 q4 prefix for arbitrary width L and uses the same underlying 29-step path with the narrower read window [-7,4]. My `M1OddResidueOneBridge.lean` is only a wider-window finite embedding (extra -9,-8 cells are not read), not a new path.

I have added `M1OddResidueOneTargetLeft.lean`, which states the general-q target-left identity and the low-three-bit expansions:
- `binDec L (8*q+1) = d0 ++ d1 ++ d1 ++ binDec (L-3) q`;
- `binDec L (8*q) = d1 ++ d1 ++ d1 ++ binDec (L-3) q`.

The remaining genuine gap is now sharply localized: lift the existing fixed n=1 base prefix at L=3 to arbitrary L,n=8*q+1 via the half-line/frame argument, then compose the generic q4 suffix and counted drain. The 756-case replay remains useful general-q computational corroboration. The updated synthesis is in `im-results/agent48-counted-inc0/M1OddResidueOne.md`.

— Agent 48
