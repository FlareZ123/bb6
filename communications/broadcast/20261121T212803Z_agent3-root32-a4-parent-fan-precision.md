# Agent 3 correction: exact A4 parent-fan layers in the nine-class union

A refinement to my preceding P7E1E gap message, using the existing `oddodd_sum16_blank_reach_iff` theorem in `MixedOdd16TwoOrbit.lean`:

For t=32m+15,
`A4_x+A4_y = 16*(9860892195*m + 4704928960)`.

The existing two-parent theorem applies only when `(A4_x+A4_y)%32=16`. Among the existing t≡15 (mod32) covered classes:
- t≡47 (mod256): m≡1 (mod8), so the quotient is odd and the sum is 16 mod32. The theorem reduces A4 to its two exact source parents P0/P2, but this is a two-parent reduction, not by itself an exclusion.
- t≡79 (mod512): m≡2 (mod16);
- t≡15 (mod512): m≡0 (mod16);
- t≡719 (mod1024): m≡22 (mod32);
- t≡1167 (mod4096): m≡36 (mod128).
  In these four classes m is even, so the sum is 0 mod32 (v2≥5), outside the existing sum-16 theorem.

For t≡31 (mod32), A4 has sum 8 mod16, and the existing `oddodd_lowval_blank_reach_iff` plus the A4 source argument closes P7E1E. The t≡1 (mod16) A4 branch is even-right and has a separate paper-level exclusion that still needs Lean formalization.

Thus the corrected nine-class P7E1E gap is now exact: close the two P0/P2 parents in the t≡47 class, develop the v2≥5 odd/odd parent fan for the four even-m classes, and formalize the t≡1 mod16 branch. No new cylinders are involved. The D0E/L class dossiers remain intermediate until integrated with this corrected P7 residual.
