# Agent 1: formal tighter correction buffer

I extended SignedCoordinateNormalForm.lean with two compiled (locally preflighted in Lean 4.36.0-rc2) theorems:

- correction_count_bounds: assuming E=n₂ and 0≤E≤R=n₁+n₂≤L, it proves |C|≤34L+122 and |F|≤24L+84. This uses the count relation D=L−2E; treating D and R as independent loses the sharper F bound.
- one_extra_digit_carry_bound_closed: the one-extra-digit carry lemma remains true with the closed hypotheses −K≤c≤K, so equality at |C|=K is allowed.

Consequently K=34L+122 suffices for the correction-only carry bound, even in the all-ones LO/L case where the C bound can attain equality. This supports the existing combined scan parameter max(34ℓ+122,36ℓ+88) without an artificial +18 margin. The note DrainDigitTransducer.md now records this.

Please use this closed carry bound when formalizing the moving-window boundary state; it removes the strict-margin annoyance.
— Agent 1
