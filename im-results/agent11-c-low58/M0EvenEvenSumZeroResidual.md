# m=0 high-ray residual: even-even sum-zero sector

Status: **intermediate analysis, not a blank-root closure theorem**. This note records the exact residual left by the existing m=0 normalizer and a first pass through its all-source predecessor grammar. Do not promote any reachability conclusion beyond the explicitly stated lemmas.

## Residual after the first two forced inverses

For the high m=0 stopping ray
[
j=7+32t,qquad k=3j+7,
]
the target is ((17+64t,,28+96t)). The first two exact inverse gates give
[
(17+64t,28+96t)
longleftarrow (43+160t,13+48t)
longleftarrow A(t):=(26+104t,18+76t).
]

For odd (t=2s+1),
[
A(t)=(130+208s,;94+152s),qquad
A_x+A_y=8(28+45s).
]
Thus (A(t)) is even-even and its coordinate sum is (0mod 8). This is exactly the case not covered by the existing nonzero-sum even-even inverse theorems:
- `EvenEvenInverse.section_even_even_iff_affine` requires the sum not be (0mod 8);
- `ExtraEvenOrbit.eveneven_nonzero_blank_reach_iff` has the same nonzero-sum restriction.

The finite six-sector census stops at this residual for odd (t); it does not decide blank-root reachability there.

## Exact parent branches visible from SectionAllInverse

Put (S=28+45s), so (A_x+A_y=8S).

1. **Low parent.** The low branch always gives
   [
   L(s)=(A_x+A_y-2,;(A_y-2)/2)
       =(222+360s,;46+76s).
   ]
   Its coordinate sum is (268+436s), hence is (4mod8) when (s) is even and (0mod8) when (s) is odd. In the even-(s) subcase the existing even-even unique-parent theorem applies to (L(s)); in the odd-(s) subcase it remains in the sum-zero sector.

2. **Even-(a) bounce parents.** For a parent with even (age2), the exact source equations require
   [
   8S=2^n(2a+4),qquad 2k+a+9+3n=A_x+2A_y.
   ]
   Since (A_x+2A_y) is even and (a) is even, the cost equation forces (n) odd. Thus possible bounce depths are (n=1,3,5,ldots), bounded by the 2-adic valuation of (8S). For (n=1) the parent is explicit:
   [
   B_1(s)=(54+90s,;126+211s).
   ]
   Its right coordinate is odd exactly when (s) is odd. In that case its coordinate sum is (180+301s), so the global odd-right image invariant excludes (B_1(s)) when (sequiv1mod4), but not when (sequiv3mod4).

3. **Exceptional low-(a) branches.** The (a=1) bounce branch is impossible because it requires (A_x+A_y+1) to be even, while this quantity is odd. The (a=0) bounce branch would require (S=2^n); for odd (s), (S) is odd and at least (73), so this is impossible. For even (s), the equation (28+45s=2^n) remains a separate arithmetic subproblem.

4. **Odd-(a) bounce branch.** It is impossible for the same parity reason: it requires the odd number (A_x+A_y+1) to equal an even power-of-two multiple.

## What remains

The hard case is the simultaneous presence of the low parent (L(s)) and one or more even-(a) bounce parents. For odd (s), only the (n=1) even-(a) bounce depth is possible, but (B_1(s)) is not excluded when (sequiv3mod4), and (L(s)) remains even-even sum-zero. For even (s), additional odd bounce depths occur according to (v_2(28+45s)), while the low parent is in the nonzero-sum sector and can be reduced further.

Next useful step: derive a reusable exact `sectionPreimageAll` classification specialized to ((x,y)=(130+208s,94+152s)), then analyze the remaining low and bounce parents together. Agent3 and Agent24 have been asked whether existing work already covers this sector; check their replies before rebuilding overlapping machinery.

Related existing files: `M0FourRoot.lean`, `M0OddRayValTwo.lean`, `CThreeDiagonalM0DeepFull.lean`, `EvenEvenInverse.lean`, `ExtraEvenOrbit.lean`, `SectionAllInverse.lean`.
