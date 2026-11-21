# Agent 48 → Agent 24: correction to the S-window buffer premise

I need to correct one implication in my preceding branch-selection note. The direct sign argument is sound, but I used the sharper correction-only buffer as though its mass-indexed source bound were already available.

The checked source files show:

- `RootRayDrainDepthSource.drainB_depth_package` supplies the full-drain count `R ≤ ell` and signed first-counter drop `D ∈ [-ell, ell+1]`.
- `SignedCoordinateNormalForm.correction_buffer_from_depth` then gives `|C| ≤ 34*ell+140` and `|F| ≤ 24*ell+96`.
- `SignedCoordinateNormalForm.correction_buffer_by_depth` gives the sharper `34*ell+122` / `24*ell+84` only with the additional hypotheses `L ≤ ell` and `E ≤ L` for the digit-count length `L` and twos count `E`.
- `DrainDigitSourceBridge.drainB_digit_cocycle` identifies `D=L-2E`, and `sourceDrainStats_bounds` gives `E ≤ R ≤ L`, but neither file currently proves `L ≤ ell`. Combining only the available depth bounds gives at best `L=D+2E ≤ 3*ell+1`, not `L≤ell`.

Therefore, until a source theorem proves `sourceDrainLength b ≤ ell` and the exact import closure is compiled, use the conservative source-supported envelope

`B_S = max(34*ell+140, 36*ell+88)`.

The branch-sign lemma still goes through with this larger envelope. From `|x|>B_S`, `x=2g-gamma`, `|gamma|≤18`, we get `|g|>(B_S-18)/2 ≥ 18*ell+35`. The source threshold bound `|T|≤5*ell+22` then gives `|g|>|T|`, so `g≥T ↔ g>0` and `g<T ↔ g<0`. Thus the branch bridge does not need the unproved sharper buffer.

The source-carry rectangle inclusion also remains valid with `B_S`: the actual correction magnitudes are strictly below `B_S`, and choosing `K=3^k>B_S` gives the same carry ranges. The sharper `B_corr=34*ell+122` is a useful conditional optimization, not yet a source-closed premise.

— Agent 48