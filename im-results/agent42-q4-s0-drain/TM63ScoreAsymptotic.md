# Near-exact leading coefficient for the TM63 champion score

**Status:** new paper-level inequality, conditional on the existing TM63 source-cost decomposition. It does not certify the uncompiled authentic-root/dispatcher composition and does not establish a BB(6) upper bound.

Let
\[
S=C_{\rm root}+D_{\rm root}+D_N,
\qquad b=b_N,
\]
be the exact score split in [TM63PublishedTowerSandwich.md](TM63PublishedTowerSandwich.md), and let \(N\) be the outer dispatcher index. The existing source-level bounds give

\[
\begin{aligned}
D_N\le{}&6b^2+60b+(6N^2+57N-66)b_{N-1}\\
&+48N+90k^2+111k+12(N+1)U+90,
\end{aligned}
\]
where \(k\le N\), \(b_{N-1}<b\), and \(U\le b\). They also give
\[
C_{\rm root}<7\cdot4^m,\qquad
D_{\rm root}\le7\cdot4^{n-1},
\]
and, with \(R=2^{n-1}-1\),
\[
R^2>9\cdot4^m,\qquad R^2>\tfrac12\,4^{n-1},\qquad b\ge2^N R.
\]
For the authentic parameters, \(N=(2^{78}-1)2^A-3\ge256\), and \(b\ge2^N\).

## Dispatcher remainder

For \(N\ge2\), the preceding inequalities imply
\[
D_N\le6b^2+E_N,
\]
where
\[
E_N\le(6N^2+69N+72)b+90N^2+159N+90.
\]
The two coefficients satisfy
\[
6N^2+69N+72\le100N^2,
\qquad
90N^2+159N+90\le200N^2.
\]
Since \(b\ge2^N\ge1\),
\[
E_N\le300N^2b.
\]
For every \(N\ge256\), \(300N^2\le2^{N/2}\). Consequently
\[
\boxed{E_N\le2^{-N/2}b^2,\qquad
D_N\le(6+2^{-N/2})b^2.}
\tag{1}
\]

## Root-prefix and initial-drain remainder

The root bounds and the two lower bounds on \(R^2\) give
\[
C_{\rm root}<\frac79R^2,
\qquad
D_{\rm root}<14R^2.
\]
Thus
\[
C_{\rm root}+D_{\rm root}
<\frac{133}{9}R^2
<15R^2
\le15\,4^{-N}b^2
<2^{-N/2}b^2,
\tag{2}
\]
where the final inequality is immediate for \(N\ge256\).

Combining (1) and (2) with the exact score split yields
\[
\boxed{
S<\bigl(6+2^{1-N/2}\bigr)b_N^2.
}
\tag{3}
\]
The exact final counted increment supplies the matching leading lower bound
\[
S\ge6(b_N+1)^2>6b_N^2.
\tag{4}
\]

Therefore the score is not merely bounded by \(9b_N^2\): conditional on the same source-cost identities, it satisfies the explicit near-equality
\[
\boxed{
6b_N^2<S_{\rm TM1}
<\bigl(6+2^{1-N/2}\bigr)b_N^2,
\qquad
1<\frac{S_{\rm TM1}}{6b_N^2}
<1+\frac{2^{-N/2}}{3}.
}
\]

The relative error is astronomically smaller than the previous factor-nine estimate. This does not improve the adjacent-tetration interval \(T_{q-1}<S<T_q\), but it identifies the exact leading coefficient of the primitive-step count with an explicit error term. It may be useful when comparing the champion's score with other long-running machines.

## Evidence boundary

This derivation uses only the paper-level inequalities and exact cost split already recorded in the linked sandwich note. It introduces no new simulation claim and no new Lean theorem. The complete authentic TM63 source composition and its transitive axiom audit remain unaccepted; keep this result in im-results/ until that gate passes. In particular, (3) is not an unconditional lower-bound certificate for BB(6), and it says nothing about the remaining six-state machines.
