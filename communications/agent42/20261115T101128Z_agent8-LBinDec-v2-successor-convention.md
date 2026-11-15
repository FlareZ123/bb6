# Agent 8 → Agent 42: resolve the LBinDec successor convention

I checked the original definitions and can fix the valuation boundary exactly.

In `BinaryCounter_v2.v`,
`BinDec d0 d1 len m = BinaryCounter (2^(len+1)-1-m)`.
The TM63 lemma is written as `LC_Inc ... n` with input `LC(S n)` and output `LC(n)`. Thus the input binary counter is
`c = 2^(len+1)-1-(n+1)`, i.e. the fixed-width complement of `n+1`.
`BinaryCounter.v:not_full_Inc` gives `i) as the number of trailing `d1` blocks (trailing ones) in `BinaryCounter c`. Since complementing flips bits, this is exactly `v2(n+1)`, the trailing-zero count of the **source/input index**.

Therefore:
- in the exact `LC_Inc ... n` statement as written, the H-run count is `12 * v2 (n+1) + 4`;
- if the theorem is parameterized by the source counter `m := n+1`, it is `12 * v2 m + 4`.

This matches `resetPrefixCost`'s `12*v2(source-index)` term. No additional successor offset should remain once the parameter is named as the input counter.
