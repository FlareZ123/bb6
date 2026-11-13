# Modulo-eleven parent obstruction for the Space Needle cancellation family

**Status:** exact arithmetic derivation; not yet Lean-compiled. This is an additional all-\(r\) residue cylinder for the cancellation-feeder inverse-parent sieve.

## Theorem

Use the cancellation family
\[
a_r=\frac{9^r+5}{2},\quad A_r=2^{a_r},\quad
P_0(A)=0,\quad P_{r+1}(A)=A^2P_r(A)+9^r(A-3),
\]
with shifted feeder target \(X_r=A_rP_r(A_r)/2\). A candidate parent of valuation \(u\) must satisfy
\[
2^{u+1}+3\mid A_rP_r(A_r)+3-2u.
\]
The physical parent range is \(u+1\le2ra_r\), which ensures the natural subtraction is not truncated.

Define the unique allowed residue \(w_r\pmod{11}\) by
\[
w_r\equiv
\begin{cases}
7+2(5^r-9^r) & r\text{ odd},\\
7+r\,3^{2r} & r\text{ even}
\end{cases}
\pmod{11}.
\]

**Modulo-eleven theorem.** For every \(r\ge1\), every physical valuation \(u+1\le2ra_r\) satisfying
\[
u\equiv2\pmod{10},\qquad u\not\equiv w_r\pmod{11}
\]
is impossible as an immediate-parent valuation of the cancellation feeder.

Thus, among the \(u\equiv2\pmod{10}\) cylinder, only the single class \(u\equiv w_r\pmod{11}\) survives modulo \(110\); the other ten classes are excluded.

## Proof

First compute \(A_r\pmod{11}\). Since \(9^2\equiv1\pmod{20}\),
\[
a_r\equiv
\begin{cases}
3\pmod{10} & r\text{ even},\\
7\pmod{10} & r\text{ odd}.
\end{cases}
\]
As \(2^{10}\equiv1\pmod{11}\), this gives
\[
A_r\equiv
\begin{cases}
8\equiv-3\pmod{11} & r\text{ even},\\
7\pmod{11} & r\text{ odd}.
\end{cases}
\]

The cancellation recurrence also gives
\[
P_r(A)=\sum_{j=0}^{2r-1}(-3)^jA^{2r-1-j}.
\tag{1}
\]

If \(r\) is odd, \(A_r\equiv7\pmod{11}\), so \(A_r+3\equiv10\) is invertible. The exact identity
\[
(A_r+3)P_r(A_r)+9^r=A_r^{2r}
\]
therefore gives, using \(7^2\equiv5\pmod{11}\),
\[
P_r(A_r)\equiv10(5^r-9^r)\pmod{11}.
\]
Consequently
\[
A_rP_r(A_r)+3
\equiv4(5^r-9^r)+3\pmod{11},
\]
and multiplying by \(6=2^{-1}\pmod{11}\) gives
\[
6(A_rP_r(A_r)+3)\equiv7+2(5^r-9^r)=w_r\pmod{11}.
\]

If \(r\) is even, \(A_r\equiv-3\pmod{11}\). In (1), every summand is then \((-3)^{2r-1}=-3^{2r-1}\), so
\[
P_r(A_r)\equiv-2r\,3^{2r-1}\pmod{11}.
\]
It follows that
\[
A_rP_r(A_r)+3
\equiv2r\,3^{2r}+3\pmod{11},
\]
and hence
\[
6(A_rP_r(A_r)+3)\equiv7+r\,3^{2r}=w_r\pmod{11}.
\]

Now suppose \(u\equiv2\pmod{10}\). Since \(2^{10}\equiv1\pmod{11}\),
\[
2^{u+1}+3\equiv2^3+3=0\pmod{11}.
\]
If the parent divisibility held, then \(11\) would divide its numerator as well:
\[
A_rP_r(A_r)+3-2u\equiv0\pmod{11}.
\]
The two parity cases above show that this forces
\[
u\equiv6(A_rP_r(A_r)+3)\equiv w_r\pmod{11}.
\]
Thus every \(u\equiv2\pmod{10}\) with \(u\not\equiv w_r\pmod{11}\) is excluded.

The physical-range hypothesis is used only to ensure \(2u\le A_rP_r(A_r)+3\), so the displayed natural subtraction agrees with the integer numerator. This follows from the existing power-dominance bound \((4r+2)a_r\le2^{a_r}=A_r\) and \(P_r(A_r)>0\).

## Improvement to the existing three-prime sieve

The existing all-\(r\) filters in CancellationMod5, CancellationMod7Joint, and CancellationMod13Joint exclude the following residue sets:

- \(E_5\): \(u\bmod20\in\{0,8,12,16\}\), density \(1/5\);
- \(E_7\): \(u\bmod3=1\) and \(u\bmod7\) is not the single allowed residue determined by \(r\bmod3\), density \(2/7\);
- \(E_{13}\): \(u\bmod12=9\) and \(u\bmod13\) is not the single allowed residue determined by \(r\bmod6\), density \(1/13\).

Their union has density \(46/91\). The new set
\[
E_{11}(r):\quad u\bmod10=2,\quad u\bmod11\ne w_r
\]
has density \(1/11\). Its overlaps are independent of the particular allowed residues \(w_r\), \(E_7(r)\), and \(E_{13}(r)\):
\[
\begin{aligned}
|E_{11}\cap E_5|&=1/22,\\
|E_{11}\cap E_7|&=2/77,\\
|E_{11}\cap E_5\cap E_7|&=1/77,\\
E_{11}\cap E_{13}&=\varnothing.
\end{aligned}
\]
For the last disjointness, \(u\equiv2\pmod{10}\) and \(u\equiv9\pmod{12}\) are incompatible modulo \(60\). The other counts follow directly by CRT; for the triple intersection, \(u\equiv12\pmod{20}\) and \(u\equiv1\pmod3\) give \(u\equiv52\pmod{60}\).

Therefore the new part of the modulo-eleven sieve outside the existing three filters has density
\[
\frac1{11}-\frac1{22}-\frac2{77}+\frac1{77}
=\frac5{154}.
\]
The combined four-prime obstruction consequently excludes
\[
\frac{46}{91}+\frac5{154}
=\boxed{\frac{1077}{2002}\approx53.7962\%}
\]
of all predecessor-valuation residue classes, uniformly for every \(r\ge1\). This is a residue-class density over the joint period, not an exact finite-interval count; boundary effects in the physical range are separate.

## Formalization route

A Lean module can reuse CancellationNat.P, CancellationNat.exact, CancellationGap.valuationA_double, CancellationGap.valuationA_linear, and CancellationStrip.P_pos. The key new lemmas are:

1. \(a_r\bmod10\) is \(3\) for even \(r\) and \(7\) for odd \(r\);
2. the odd/even formulas for \(P_r(A_r)\bmod11\) above;
3. the one-step implication \(11\mid2^{u+1}+3\) when \(u\bmod10=2\);
4. CRT counting for the new disjoint residue contribution \(5/154\).

This result only removes a residue cylinder of possible inverse parents. It does not prove that the remaining parents are absent, that the cancellation feeder is unreachable from the blank start, or that BB(6) is solved.
