# Modulo-twenty-nine parent obstruction for the Space Needle cancellation family

**Status:** exact arithmetic derivation; not yet Lean-compiled. This adds a sixth prime to the cancellation-feeder inverse-parent residue sieve.

## Theorem

Let
\[
a_r=\frac{9^r+5}{2},\quad A_r=2^{a_r},\quad
P_0(A)=0,\quad P_{j+1}(A)=A^2P_j(A)+9^j(A-3).
\]
A physical candidate parent of valuation \(u\) satisfies
\[
u+1\le2ra_r,\qquad
2^{u+1}+3\mid A_rP_r(A_r)+3-2u.
\]

Let \(\bar A_r\in\mathbb Z/29\mathbb Z\) be
\[
\bar A_r=
\begin{cases}
8 & r\equiv0\pmod3,\\
12 & r\equiv1\pmod3,\\
27 & r\equiv2\pmod3.
\end{cases}
\]
The three values \(\bar A_r^2-9\) are respectively \(26,19,24\), with inverses \(19,26,23\). Thus the geometric-sum formula gives the following division-free residues:
\[
\bar P_r\equiv
\begin{cases}
8(6^r-9^r) & r\equiv0\pmod3,\\
2(28^r-9^r) & r\equiv1\pmod3,\\
4^r-9^r & r\equiv2\pmod3
\end{cases}
\pmod{29}.
\]
Define \(w_r:=15(\bar A_r\bar P_r+3)\pmod{29}\).

**Modulo-twenty-nine theorem.** For every \(r\ge1\), if
\[
u\equiv18\pmod{28},\qquad u\not\equiv w_r\pmod{29},
\]
then \(u\) cannot be the valuation of an immediate parent of the cancellation feeder.

Thus, within the \(u\equiv18\pmod{28}\) cylinder, only one of the twenty-nine residue classes modulo \(812\) survives; the other twenty-eight are excluded.

## Proof

For \(r\ge1\), \(9^r\equiv9\pmod{56}\), since \(9^3=729\equiv1\pmod{56}\). Therefore
\[
2a_r=9^r+5\equiv
\begin{cases}
6 & r\equiv0\pmod3,\\
14 & r\equiv1\pmod3,\\
30 & r\equiv2\pmod3
\end{cases}
\pmod{56},
\]
so
\[
a_r\equiv3,7,15\pmod{28}
\]
in the respective cases. Since \(2^{14}\equiv-1\pmod{29}\), this yields
\[
A_r=2^{a_r}\equiv8,12,27\pmod{29},
\]
as claimed.

For a fixed \(A=A_r\), the recurrence has the closed form
\[
P_r(A)=(A-3)\sum_{j=0}^{r-1}A^{2(r-1-j)}9^j.
\]
Because \(A^2-9\not\equiv0\pmod{29}\) for the three possible residues, the geometric sum gives
\[
P_r(A_r)\equiv
(\bar A_r-3)(\bar A_r^{2r}-9^r)(\bar A_r^2-9)^{-1}
=\bar P_r\pmod{29}.
\]

If \(u\equiv18\pmod{28}\), then \(u+1\equiv19\pmod{28}\). Since \(2^{14}\equiv-1\pmod{29}\),
\[
2^{u+1}+3\equiv2^{19}+3
\equiv-2^5+3
\equiv-32+3
\equiv0\pmod{29}.
\]
If the parent divisibility held, its numerator would also be divisible by \(29\), forcing
\[
2u\equiv A_rP_r(A_r)+3
\equiv\bar A_r\bar P_r+3\pmod{29}.
\]
As \(2^{-1}\equiv15\pmod{29}\), this says \(u\equiv w_r\pmod{29}\), proving the theorem.

The physical-range hypothesis ensures the natural subtraction in the parent numerator is not truncated, by the existing power-dominance and positivity lemmas.

## Improvement to the combined residue sieve

Let \(E_{29}(r)\) be the new excluded set
\[
u\equiv18\pmod{28},\qquad u\not\equiv w_r\pmod{29}.
\]
It has density \(1/29\). It is disjoint from the existing \(E_5,E_7,E_{13},E_{19}\) sets:
- \(u\equiv18\pmod{28}\) gives \(u\equiv2\pmod4\), whereas \(E_5\) requires \(u\equiv0\pmod4\);
- it gives \(u\equiv0\pmod3\), whereas \(E_7\) requires \(u\equiv1\pmod3\);
- it gives \(u\equiv2\pmod4\), whereas \(E_{13}\) requires \(u\equiv1\pmod4\);
- it is even, whereas \(E_{19}\) requires \(u\equiv3\pmod{18}\), which is odd.

Its only overlap with the existing five-prime union is \(E_{11}\). The two valuation cylinders \(u\equiv18\pmod{28}\) and \(u\equiv2\pmod{10}\) combine to \(u\equiv102\pmod{140}\). Applying the mod-\(29\) and mod-\(11\) exclusions leaves intersection density
\[
\frac1{140}\cdot\frac{28}{29}\cdot\frac{10}{11}
=\frac2{319}.
\]
Thus the new part outside the existing union has density
\[
\frac1{29}-\frac2{319}=\frac9{319}.
\]
The six-prime union consequently excludes
\[
\frac{21541}{38038}+\frac9{319}
=\boxed{\frac{655811}{1103102}\approx59.4515\%}
\]
of all predecessor-valuation residue classes, uniformly in \(r\). This is a residue-class density over the joint period, not an exact finite-range proportion.

## Formalization route and limits

A Lean proof can reuse the existing cancellation recurrence and physical-range lemmas. The new residue calculation needs \(9^r\bmod56\), the three values of \(A_r\bmod29\), and the closed geometric-sum identity for \(P_r(A_r)\bmod29\).

This filter removes only one residue cylinder of possible inverse parents. It does not eliminate all parents, prove blank-root unreachability, or solve BB(6).
