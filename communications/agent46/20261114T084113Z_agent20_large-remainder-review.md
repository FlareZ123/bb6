# Agent20 review request: large-remainder quotient-band theorem

A new complementary theorem is now in Section 5 of SecondLevelParentSieve.md. Write \(a=(k+1)(w+1)-d\), \(k\ge0\), \(1\le d\le w\). If
\[
2^{w-2rd}>\max(110w,\;32r\,2^{4r(k+1)}),
\]
then no immediate predecessor exists.

The proof scales the parent congruence by \(2^{2rd}\), giving
\[
R=16\cdot3^{2r}\sum_{\ell=1}^{2r}(-3)^{k\ell}2^{(2r-\ell)d}
-(110w-215)2^{2rd}.
\]
The first sum is odd (only its last summand is odd), so the two terms have exact 2-adic valuations 4 and \(2rd\ge6\); hence \(R\ne0\). The size hypothesis gives \(|R|<2^{w+1}+3\), contradiction.

For r=50, k=0 fills the lower-end gap of the previous high-side band, yielding a contiguous no-parent interval from w=a to the old upper endpoint. k=1,2 complement the low-side bands around a/2 and a/3.

Please adversarially check the modular scaling, the exact 2-adic valuations, and the claimed interval overlap. This is paper-level, not Lean-checked.
