# #746: root-sensitive 27-adic restriction at the high-q t=2 odd gap

**Scope.** A new necessary condition for the authentic post-blank C(2,0) reset orbit of Cryptids machine #746. It sharpens the previously open source high-q t=2 odd continuation in the n≡5 mod6 sector. It does **not** decide whether this machine halts or determine BB(6).

**Verification.** The pure arithmetic module [GapTZeroGeometry.lean](GapTZeroGeometry.lean) compiled locally in Lean 4.36.0-rc2, with only standard logical axioms. The source-root [GapTZeroRoot.lean](GapTZeroRoot.lean) compiled locally against precise theorem-signature stubs. Full unchanged-source compilation is being checked via the [manual Agent10 workflow](../../.github/workflows/agent10-ray-odd-strip.yml). **Until that CI succeeds, the source-root assertion remains a candidate theorem, rather than fully source-certified.**

## The exact necessary gate

Use the parameters of the already source-certified [Agent7 high-q t=2 odd continuation](../agent7-fatal-density/TThreeHighTTwoOne.md). Let n≥20, s=2^(n−8), k=n−8, and retain its full source high-q margin and six exact source predecessor equations:

- 2*ray(n,j)+5=81*d0, 16*d0=2^n+q+n+2;
- 2*q+5=81*e, 16*e=8*2^(n−6)+r+n−1;
- 2*r+5=27*d, 8*d=8*s+a+k+5.

The four successive even candidates b,c,f,g are defined by

\[
2a=8s+b+k,\quad2b=8s+c+k,\quad
2c=8s+f+k,\quad2f=8s+g+k.
\]

The new theorem, named high_ttwo_one_forced_d_g27, proves under the exact original-source hypotheses:

\[
\boxed{
n\bmod6=5,\quad
(n\bmod18,d\bmod9)\in\{(5,1),(11,4),(17,7)\},
\quad \mathrm{Reach}_{C(2,0)}(a)
\ \Longrightarrow\ 27\mid(2g+5).
}
\]

The authentic root hypothesis is essential. The conclusion describes a necessary gate on a hypothetical reachable ancestor.

## Mathematical mechanism

The source-checked upper and lower estimates for r, plus the elementary 200n≤s, sharpen Agent7's previous 1973s≤1000d≤1979s to

\[
1974s\le1000d\le1977s.
\]

Substitution into the four even equations gives

\[
9s+6k+12<2g+5,\qquad
2(2g+5)+12<21s.
\]

A rooted g in the even-image gap must have an actual odd reset predecessor x. The complete exact first-reset grammar assigns an exponent t≥0 and a quotient z with

\[
2g+5=3^{t+1}z,\quad
6\cdot2^\ell+1\le2^t z\le8\cdot2^\ell-1,\quad
2^{t+1}z=8\cdot2^\ell+x+\ell+5.
\]

For t=1, the interval for 2z falls strictly between all odd-image bands, excluding the predecessor outright. For t=0, the image band forces ℓ=k−1 and puts x in a strict even-image gap, 2s<x and 2x+2<6s. The forced quotient congruences yield 9|(2g+5), hence 3|z. For n mod6=5, the exact source scale also gives x mod3=0. The existing source theorem root_excludes_nonimage then excludes the true-root reachability of x. Therefore any genuine rooted predecessor requires t≥2 and hence 27|(2g+5).

This newly excludes the t=0 branch **using the genuine blank-root condition**, beyond the purely arithmetic t=1 exclusion.

## Quotient classes modulo 27

The even equations imply the exact identity

\[
2g+5+496s+62k+155=256d.
\]

Since 256 is invertible modulo27 and 2 has order18 modulo27, the necessary d residue is uniquely determined by n modulo54:

| n mod54 | 5 | 11 | 17 | 23 | 29 | 35 | 41 | 47 | 53 |
|---|---|---|---|---|---|---|---|---|---|
| Required d mod27 | 19 | 22 | 25 | 1 | 4 | 7 | 10 | 13 | 16 |

This arithmetic table follows from the source equations and the 27-gate, without assuming any probability model. It removes two of three formal quotient lifts within each of the selected d mod9 classes.

## Remaining obstacle

Odd predecessors with t≥2 remain possible, as do n mod6=4 and the earlier 9-gate alternatives. The result should guide a root-sensitive analysis of t≥2 odd branches instead of another finite cutoff or unrooted density census. Full #746 blank-root halting and the BB(6) value remain open.
