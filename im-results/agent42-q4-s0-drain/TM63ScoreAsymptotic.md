# Near-exact final-increment bound for the TM63 champion score

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
For the authentic parameters, \(N=(2^{78}-1)2^A-3\ge256\). Here \(R=V_{M+46}\ge V_0=63\), and the dispatcher recurrence starts at \(b_0=R\), so \(b_{N-1}\ge R\), \(b\ge2^N R\), and \(b\ge2^{256}\).

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
\boxed{E_N<60.51b,\qquad D_N<6b^2+60.51b.}
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
C_{\rm root}+D_{\rm root}<\frac{133}{9}R^2.
\]
Since \(b\ge2^R-1\), \(R\ge63\), and
\[
2^R-1>\frac{133000}{9}R^2\qquad(R\ge63),
\]
we obtain the useful comparison
\[
\boxed{C_{\rm root}+D_{\rm root}<\frac b{1000}.}
\tag{2}
\]
(The displayed exponential inequality is immediate at \(R=63\), and \((2^R-1)/R^2\) is increasing for \(R\ge63\).)

Combining (1) and (2) with the exact score split gives
\[
S<6b^2+60.511b.
\]
The exact final counted increment from [DirectTerminalTetrationBound.md](../agent24-champion-time/DirectTerminalTetrationBound.md) is already a lower bound:
\[
S\ge6(b+1)^2=6b^2+12b+6.
\]
Since \(60.511b<61b+6\), the full score therefore satisfies the sharper additive estimate
\[
\boxed{
6(b_N+1)^2\le S_{\rm TM1}
<6(b_N+1)^2+49b_N.
}
\tag{3}
\]
Equivalently, all work before and outside the final counted increment contributes fewer than \(49b_N\) additional primitive steps.

The relative excess over the final counted increment is consequently bounded by
\[
0\le
\frac{S_{\rm TM1}}{6(b_N+1)^2}-1
<\frac{49b_N}{6(b_N+1)^2}
<\frac{49}{6b_N}
\le\frac{49}{6\cdot63\cdot2^{256}}
<1.2\times10^{-78}.
\]
This is a much sharper description than the earlier factor-nine estimate or the adjacent-tetration interval. It identifies the final counted increment as the score's leading term with a tiny explicit additive remainder. It may be useful when comparing the champion's score with other long-running machines.

## Evidence boundary

This derivation uses only the paper-level inequalities and exact cost split already recorded in the linked sandwich note. It introduces no new simulation claim and no new Lean theorem. The complete authentic TM63 source composition and its transitive axiom audit remain unaccepted; keep this result in im-results/ until that gate passes. In particular, (3) is not an unconditional lower-bound certificate for BB(6), and it says nothing about the remaining six-state machines.
