# Modulo-nineteen parent obstruction for the Space Needle cancellation family

**Status:** exact arithmetic derivation; not yet Lean-compiled. This adds a fifth prime to the cancellation-feeder inverse-parent residue sieve.

## Theorem

Use
\[
a_r=\frac{9^r+5}{2},\quad A_r=2^{a_r},\quad
P_0(A)=0,\quad P_{j+1}(A)=A^2P_j(A)+9^j(A-3).
\]
A physical candidate parent of valuation \(u\) satisfies
\[
u+1\le2ra_r,\qquad
2^{u+1}+3\mid A_rP_r(A_r)+3-2u.
\]

Define
\[
w_r:=11+6(6^r-9^r)\pmod{19}.
\]

**Modulo-nineteen theorem.** For every \(r\ge1\), if
\[
u\equiv3\pmod{18},\qquad u\not\equiv w_r\pmod{19},
\]
then \(u\) cannot be the valuation of an immediate parent of the cancellation feeder.

Thus, within the \(u\equiv3\pmod{18}\) cylinder, only one of the nineteen residue classes modulo \(342\) survives; eighteen are excluded.

## Proof

For every \(r\ge1\), \(9^r\equiv9\pmod{36}\), since \(9^2\equiv9\pmod{36}\). Therefore
\[
2a_r=9^r+5\equiv14\pmod{36},
\qquad a_r\equiv7\pmod{18}.
\]
As \(2^{18}\equiv1\pmod{19}\),
\[
A_r=2^{a_r}\equiv2^7=128\equiv14\pmod{19}.
\]
Consequently \(A_r^2\equiv6\) and \(A_r-3\equiv11\pmod{19}\). For the fixed value \(A=A_r\), the recurrence becomes
\[
P_{j+1}(A)\equiv6P_j(A)+11\cdot9^j\pmod{19}.
\]
Starting from \(P_0=0\), induction gives
\[
P_r(A_r)\equiv9(6^r-9^r)\pmod{19}.
\]
Hence
\[
A_rP_r(A_r)+3
\equiv14\cdot9(6^r-9^r)+3
\equiv12(6^r-9^r)+3\pmod{19}.
\]

If \(u\equiv3\pmod{18}\), then \(u+1\equiv4\pmod{18}\), and
\[
2^{u+1}+3\equiv2^4+3=16+3=0\pmod{19},
\]
using \(2^{18}\equiv1\pmod{19}\). If the parent divisibility held, its numerator would also be divisible by \(19\), forcing
\[
2u\equiv12(6^r-9^r)+3\pmod{19}.
\]
Since \(2^{-1}\equiv10\pmod{19}\),
\[
u\equiv10\bigl(12(6^r-9^r)+3\bigr)
\equiv6(6^r-9^r)+11=w_r\pmod{19}.
\]
This proves the theorem.

The physical-range hypothesis ensures \(2u\le A_rP_r(A_r)+3\), so the natural subtraction in the displayed numerator is not truncated; this follows from the existing power-dominance bound and positivity of \(P_r(A_r)\).

## Improvement to the combined residue sieve

Let \(E_{19}(r)\) be the new excluded set
\[
u\equiv3\pmod{18},\qquad u\not\equiv w_r\pmod{19}.
\]
It has density \(1/19\). It is disjoint from the existing \(E_5,E_7,E_{11}\) sets:
- \(u\equiv3\pmod{18}\) is odd, whereas \(E_5\) and \(E_{11}\) require even residues;
- \(u\equiv3\pmod{18}\) implies \(u\equiv0\pmod3\), whereas \(E_7\) requires \(u\equiv1\pmod3\).

Its intersection with \(E_{13}\) has density
\[
\frac1{36}\cdot\frac{12}{13}\cdot\frac{18}{19}
=\frac6{247},
\]
because \(u\equiv3\pmod{18}\) and \(u\equiv9\pmod{12}\) are equivalent to \(u\equiv21\pmod{36}\), and the remaining mod-\(13\) and mod-\(19\) exclusions each remove all but one residue.

The five-prime union therefore gains
\[
\frac1{19}-\frac6{247}=\frac7{247}
\]
beyond the four-prime density \(1077/2002\). Its total residue-class coverage is
\[
\frac{1077}{2002}+\frac7{247}
=\boxed{\frac{21541}{38038}\approx56.6302\%}.
\]
This is a uniform residue-class density over the joint period, not an exact finite-range proportion.

## Formalization route and limits

A Lean proof can reuse CancellationNat.P and the existing physical-range and positivity lemmas. New residue lemmas needed are \(a_r\equiv7\pmod{18}\), \(A_r\equiv14\pmod{19}\), and the recurrence identity \(P_r(A_r)\equiv9(6^r-9^r)\pmod{19}\).

This filter removes only one residue cylinder of possible inverse parents. It does not eliminate all parents, prove blank-root unreachability, or solve BB(6).
