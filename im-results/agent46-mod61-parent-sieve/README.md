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

For every \(r\ge1\), \(9^r\equiv9\pmod{120}\) when \(r\) is odd and \(9^r\equiv81\pmod{120}\) when \(r\) is even, since \(9^2\equiv81\pmod{120}\) and \(9^3\equiv9\pmod{120}\), so the powers alternate from exponent one onward. Thus
\[
a_r\equiv7\pmod{60}\quad(r\text{ odd}),\qquad
a_r\equiv43\pmod{60}\quad(r\text{ even}).
\]
Since \(2^6\equiv3\pmod{61}\), we have \(2^{30}\equiv3^5=243\equiv-1\pmod{61}\). This yields
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

## Corrected combined residue sieve

The u ≡ 35 (mod 60) cylinder is disjoint from the six earlier filters, including the corrected E29 cylinder u ≡ 18 (mod 28). Thus E61 adds exactly 1/61 to the corrected six-prime coverage. The resulting seven-prime residue-class density is:
- 3,162,121/5,176,094 ≈ 61.0909% when r ≡ 1 (mod 3);
- 3,113,443/5,176,094 ≈ 60.1504% when r ≡ 0 or 2 (mod 3).

These are exact residue-class densities over the joint period, not exact finite-range proportions. The r-dependence comes from the E29/E7 overlap documented in [the corrected modulo-29 audit](../agent46-mod29-parent-sieve/README.md).


## Formalization route and limits

A Lean proof can reuse the existing cancellation recurrence and physical-range lemmas. The new residue calculations need \(9^r\bmod120\), the two values of \(A_r\bmod61\), and the closed geometric-sum identity for \(P_r(A_r)\bmod61\).

This filter removes only one residue cylinder of possible inverse parents. It does not eliminate all parents, prove blank-root unreachability, or solve BB(6).
