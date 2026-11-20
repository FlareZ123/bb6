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
where \(k\le N\), \(b_{N-1}<b\), and \(U\le R\). They also give
\[
C_{\rm root}<7\cdot4^m,\qquad
D_{\rm root}\le7\cdot4^{n-1},
\]
and, with \(R=2^{n-1}-1\),
\[
R^2>9\cdot4^m,\qquad R^2>\tfrac12\,4^{n-1},\qquad b\ge2^N R.
\]
For the authentic parameters, \(N=(2^{78}-1)2^A-3\ge256\), \(R\ge63\), and \(b\ge2^N R\ge2^{256}\).

## Dispatcher remainder

The recurrence is \(b_j=2^{b_{j-1}}-1\), so \(b=2^{b_{N-1}}-1\). Since \(b_{N-1}\ge R\ge63\), the elementary inequality \(x^4\le2^x-1\) for \(x\ge63\) gives
\[
b_{N-1}\le b^{1/4}.
\]
Also \(N^4\le2^N\le b\) for \(N\ge256\), hence \(N\le b^{1/4}\).

Write \(D_N\le6b^2+E_N\). Since \(6N^2+57N-66\le6N^2+57N\), \(k\le N\), and \(U\le R\le b/2^N\), the dispatcher formula gives
\[
\begin{aligned}
E_N\le{}&60b
 +(6N^2+57N)b_{N-1}
 +90N^2+159N+90\\
 &+12(N+1)R\\
\le{}&60b
 +6b^{3/4}+147b^{1/2}+159b^{1/4}+90
 +12(N+1)2^{-N}b.
\end{aligned}
\]
For \(N\ge256\), \(12(N+1)2^{-N}<1/100\). Since \(b\ge2^{256}\),
\[
6b^{3/4}+57b^{1/2}<\frac b4,\qquad
90b^{1/2}+159b^{1/4}+90<\frac b4.
\]
Therefore
\[
\boxed{E_N<61b,\qquad D_N<(6+61/2^N)b^2.}
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
\le\frac{133}{9\cdot4^N}b^2,
\tag{2}
\]
where the non-strict step uses \(b\ge2^N R\).

Combining (1) and (2) with the exact score split yields
\[
\boxed{
S<\left(6+\frac{61}{2^N}+\frac{133}{9\cdot4^N}\right)b_N^2.
}
\tag{3}
\]
The exact final counted increment supplies the matching leading lower bound
\[
S\ge6(b_N+1)^2>6b_N^2.
\tag{4}
\]

Therefore the score satisfies the conditional near-equality
\[
\boxed{
6b_N^2<S_{\rm TM1}
<\left(6+\frac{61}{2^N}+\frac{133}{9\cdot4^N}\right)b_N^2,
\qquad
1<\frac{S_{\rm TM1}}{6b_N^2}
<1+\frac{61}{6\cdot2^N}+\frac{133}{54\cdot4^N}.
}
\]

The coefficient excess \(61/2^N+133/(9\cdot4^N)\) decreases for \(N\ge3\); at \(N=256\) it is less than \(5.3\times10^{-76}\). The relative excess is then less than \(8.9\times10^{-77}\), and the authentic \(N\) is much larger still. This does not improve the adjacent-tetration interval \(T_{q-1}<S<T_q\), but it pins down the leading coefficient of the primitive-step count with an explicit error term. It may be useful when comparing the champion's score with other long-running machines.

## Evidence boundary

This derivation uses only the paper-level inequalities and exact cost split already recorded in the linked sandwich note. It introduces no new simulation claim and no new Lean theorem. The complete authentic TM63 source composition and its transitive axiom audit remain unaccepted; keep this result in im-results/ until that gate passes. In particular, (3) is not an unconditional lower-bound certificate for BB(6), and it says nothing about the remaining six-state machines.
