# Modulo-sixty-one parent obstruction for the Space Needle cancellation family

**Status:** exact arithmetic derivation; not yet Lean-compiled. This adds a seventh prime to the cancellation-feeder inverse-parent residue sieve.

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

For \(r\ge1\), define
\[
\bar A_r=
\begin{cases}
6 & r\text{ odd},\\
43 & r\text{ even},
\end{cases}
\qquad
\bar P_r=
\begin{cases}
34(36^r-9^r) & r\text{ odd},\\
4(19^r-9^r) & r\text{ even},
\end{cases}
\pmod{61},
\]
and
\[
w_r:=31(\bar A_r\bar P_r+3)\pmod{61}.
\]

**Modulo-sixty-one theorem.** For every \(r\ge1\), if
\[
u\equiv35\pmod{60},\qquad u\not\equiv w_r\pmod{61},
\]
then \(u\) cannot be the valuation of an immediate parent of the cancellation feeder.

Thus, within the \(u\equiv35\pmod{60}\) cylinder, only one of the sixty-one residue classes modulo \(3660\) survives; the other sixty are excluded.

## Proof

For every \(r\ge1\), \(9^r\equiv9\pmod{120}\) when \(r\) is odd and \(9^r\equiv81\pmod{120}\) when \(r\) is even, since \(9^2\equiv81\pmod{120}\) and \(9^3\equiv9\pmod{120}\). Thus
\[
a_r\equiv7\pmod{60}\quad(r\text{ odd}),\qquad
a_r\equiv43\pmod{60}\quad(r\text{ even}).
\]
As \(2^{30}\equiv-1\pmod{61}\), this yields
\[
A_r=2^{a_r}\equiv6\pmod{61}\quad(r\text{ odd}),\qquad
A_r\equiv43\pmod{61}\quad(r\text{ even}).
\]

For fixed \(A=A_r\), the recurrence has the closed form
\[
P_r(A)=(A-3)\sum_{j=0}^{r-1}A^{2(r-1-j)}9^j.
\]
When \(r\) is odd, \(A\equiv6\), so \(A^2\equiv36\), \(A-3\equiv3\), and \(36-9=27\) has inverse \(52\) modulo \(61\). Hence
\[
P_r(A_r)\equiv3(36^r-9^r)52
\equiv34(36^r-9^r)=\bar P_r\pmod{61}.
\]
When \(r\) is even, \(A\equiv43\), so \(A^2\equiv19\), \(A-3\equiv40\), and \(19-9=10\) has inverse \(55\). Hence
\[
P_r(A_r)\equiv40(19^r-9^r)55
\equiv4(19^r-9^r)=\bar P_r\pmod{61}.
\]

If \(u\equiv35\pmod{60}\), then \(u+1\equiv36\pmod{60}\). Since \(2^{30}\equiv-1\pmod{61}\),
\[
2^{u+1}+3\equiv2^{36}+3
\equiv-2^6+3
\equiv-64+3
\equiv0\pmod{61}.
\]
If the parent divisibility held, its numerator would also be divisible by \(61\), forcing
\[
2u\equiv A_rP_r(A_r)+3
\equiv\bar A_r\bar P_r+3\pmod{61}.
\]
As \(2^{-1}\equiv31\pmod{61}\), this says \(u\equiv w_r\pmod{61}\), proving the theorem.

The physical-range hypothesis ensures the natural subtraction in the parent numerator is not truncated, by the existing power-dominance and positivity lemmas.

## Improvement to the combined residue sieve

The new excluded set \(E_{61}(r)\) has density \(1/61\). Its valuation cylinder \(u\equiv35\pmod{60}\) is disjoint from all six previous filters:
- \(u\bmod20=15\), not one of the \(E_5\) residues;
- \(u\bmod3=2\), not the \(E_7\) residue \(1\);
- \(u\bmod12=11\), not the \(E_{13}\) residue \(9\);
- \(u\bmod10=5\), not the \(E_{11}\) residue \(2\);
- \(u\bmod18=17\), not the \(E_{19}\) residue \(3\);
- \(u\bmod28=7\), not the \(E_{29}\) residue \(18\).

Thus the seven-prime union adds exactly \(1/61\) beyond the six-prime density \(655811/1103102\):
\[
\frac{655811}{1103102}+\frac1{61}
=\boxed{\frac{3162121}{5176094}\approx61.0909\%}.
\]
This is a residue-class density over the joint period, not an exact finite-range proportion.

## Formalization route and limits

A Lean proof can reuse the existing cancellation recurrence and physical-range lemmas. The new residue calculations need \(9^r\bmod120\), the two values of \(A_r\bmod61\), and the closed geometric-sum identity for \(P_r(A_r)\bmod61\).

This filter removes only one residue cylinder of possible inverse parents. It does not eliminate all parents, prove blank-root unreachability, or solve BB(6).
