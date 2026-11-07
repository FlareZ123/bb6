# Exact weighted-sum identity for the S4 drain

This note records a kernel-checked identity for the drain transducer used in the S4 reduction. It is an intermediate result; it does not decide whether the authentic S4 orbit halts.

## Definitions

For a finite list \(T=[b_0,\ldots,b_{m-1}]\), define
\[
W(T)=\sum_{i=0}^{m-1}(b_i+1)2^i.
\]
The Lean file reproduces the recursive drain \(H(a,T)\) and defines the truncated weighted moment \(M_j(T)\) by
\[
M_0(T)=W(T),\qquad M_j([])=0\quad(j>0),
\]
\[
M_{j+1}(b::S)=b+1+2\bigl(M_j(S)+W(S)\bigr).
\]
Equivalently,
\[
M_j(T)=\sum_{i=0}^{m-1}\min(i+1,j+1)(b_i+1)2^i.
\]
Thus, once \(j\ge |T|\), the truncation disappears and
\[
M_j(T)=M_{\mathrm{full}}(T)
=\sum_{i=0}^{m-1}(i+1)(b_i+1)2^i.
\]

## Main theorem

Put \(X=a+1+2W(T)\) and \(j=v_2(X)\), where \(v_2\) is the exponent of 2 in a positive integer. For every successful drain \(H(a,T)=U\), Lean proves
\[
\boxed{2W(U)+2M_j(T)=(j+3)X+3\cdot 2^j.}
\]

The proof is by structural induction on the input list, with strong induction on \(a\) for the empty-list branch. In the odd-carry branch, the identities
\[
X=2X',\qquad
M_{j+1}(b::S)=b+1+2(M_j(S)+W(S))
\]
make the induction step exact. The even-carry and terminal branches reduce to elementary arithmetic.

A useful specialization applies when the carry reaches or passes the end of the list, \(j\ge |T|\):
\[
\boxed{2W(U)+2M_{\mathrm{full}}(T)=(j+3)X+3\cdot 2^j.}
\]
If additionally \(X=2^j q\) with \(q\) odd, then
\[
W(U)+M_{\mathrm{full}}(T)
=2^{j-1}\bigl((j+3)q+3\bigr)
\quad (j\ge1).
\]
This exposes the full first weighted moment of the input stack in the output potential. It is a natural statistic to track when composing successive drains.

## Verification

S4WeightFormula.lean is self-contained and uses only Lean core plus the core omega tactic. It was checked locally with Lean 4.36.0-rc2. The file prints the axiom dependencies of both the main theorem and its full-moment corollary; neither proof uses sorryAx.

## Research significance and limitation

The identity is exact for every successful drain input, not merely for the authentic root. It gives an algebraic relation between the output weighted value, the input's truncated first moment, and the 2-adic valuation of the gate potential. The full-moment specialization is particularly relevant at length-expanding gate exposures.

This does not show that the authentic S4 orbit avoids a power-of-two gate. The unresolved task is to control the moment (or a suitable finite collection of moments) through the three-drain composition \(P=G_{219}\circ G_{290}\circ G_{509}\), and to determine whether the resulting odd quotient can ever be 1.
