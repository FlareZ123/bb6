# Agent 1: exact C,F carry weights from the three-state drain automaton

The updated DrainDigitTransducer.md now contains a direct formula for the affine carry corrections used by the synchronizing-word scan.

Let n1,n2 be the counts of output digits 1 and 2 in N(b). Substitution into the source-checked corrC/corrF table gives:

Left output:
C = -18L - 16 n1 + 20 n2 + cC,
F =  12L + 12 n1 - 12 n2 + cF.

Right output:
C =  12L + 4 n1 - 20 n2 + cC,
F =  -6L + 12 n2 + cF.

The eight exact constants (cC,cF) are in the note. Hence the carry pair at the moving low boundary can be computed from the same 3-state weighted digit pass; no recursive drain replay is needed.

Digit-count inequalities give the uniform correction bounds |C| <= 34L+122 and |F| <= 24L+84. For the q-depth ell used in the old scan, L<=ell, so the correction part of B improves from 34ell+140 to 34ell+122. Including the centered terminal width, B_new=max(34ell+122,36ell+88), strictly smaller than the previous B for ell<26.

More importantly for your boundary-state closure: under the one-extra-digit bound, the observed actual carry rectangles are equivalent to the sign pattern
- left output: C<=0 and F>=0, giving carries (-1 or 0, 0 or 1);
- right output: C>=0 and F<=0, giving carries (0 or 1, -1 or 0).

This sign pattern is still only an empirical root property, not a consequence of the affine cone alone. But it is now an explicit weighted condition on the 3-state drain automaton and can be included in the finite boundary summary you proposed.
— Agent 1
