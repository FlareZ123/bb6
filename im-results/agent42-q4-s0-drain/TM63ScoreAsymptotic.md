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
For \(N\ge256\), \(12(N+1)2^{-N}<10^{-3}\). Since \(b\ge2^{256}\),
\[
6b^{3/4}+57b^{1/2}<10^{-3}b,\qquad
90b^{1/2}+159b^{1/4}+90<10^{-3}b.
\]
Therefore
\[
\boxed{E_N<60.003b,\qquad D_N<6b^2+60.003b.}
\tag{1}
\]

## Root-prefix and initial-drain remainder

The root bounds and the two lower bounds on \(R^2\) give
\[
C_{\rm root}<\frac79R^2,
\qquad
D_{\rm root}<14R^2,
\]
so
\[
C_{\rm root}+D_{\rm root}<\frac{133}{9}R^2.
\]
Since \(b\ge2^R-1\), \(R\ge63\), and
\[
2^R-1>\frac{133000}{9}R^2\qquad(R\ge63),
\]
we obtain
\[
\boxed{C_{\rm root}+D_{\rm root}<\frac b{1000}.}
\tag{2}
(The displayed exponential inequality holds at \(R=63\), and \((2^R-1)/R^2\) is increasing for \(R\ge63\).)

Combining (1) and (2) with the exact score split gives
\[
S<6b^2+60.004b<6b^2+60.01b.
\]
The exact final summand in the one-dimensional dispatcher-plus-terminal cost formula, derived in [DirectTerminalTetrationBound.md](../agent24-champion-time/DirectTerminalTetrationBound.md), is
\[
6\cdot4^{b_{N-1}}+42\cdot2^{b_{N-1}}+3b_{N-1}
=6(b+1)^2+42(b+1)+3b_{N-1}.
\]
All other dispatcher summands and the root/drain prefix costs are nonnegative, so
\[
S\ge6(b+1)^2+42(b+1)+3b_{N-1}.
\]
Since \(6b^2+60.01b=6(b+1)^2+48.01b-6\), the full score satisfies the sharper two-sided additive estimate
\[
\boxed{
6(b_N+1)^2+42(b_N+1)+3b_{N-1}
\le S_{\rm TM1}
<6(b_N+1)^2+48.01b_N-6.
}
\tag{3}
\]
Equivalently,
\[
6b_N^2+54b_N+48+3b_{N-1}
\le S_{\rm TM1}
<6b_N^2+60.01b_N.
\]
In particular, the normalized linear correction satisfies
\[
54<
\frac{S_{\rm TM1}-6b_N^2}{b_N}
<60.01.
\]
Thus the cost outside the exact final dispatcher summand is fewer than \(6.01b_N-48-3b_{N-1}<6.01b_N\) additional primitive steps.

The relative excess over the quadratic final-increment term is pinned to a narrow interval:
\[
\frac{7}{b_N+1}
<
\frac{S_{\rm TM1}}{6(b_N+1)^2}-1
<
\frac{48.01b_N-6}{6(b_N+1)^2}
<
\frac{48.01}{6b_N}
\le\frac{48.01}{6\cdot63\cdot2^{256}}
<1.1\times10^{-78}.
\]
This identifies not only the quadratic leading term but also its linear correction to within fewer than \(6.01b_N\) steps. It may be useful when comparing the champion's score with other long-running machines.

## Evidence boundary

This derivation uses only the paper-level inequalities and exact cost split already recorded in the linked sandwich note. It introduces no new simulation claim and no new Lean theorem. The complete authentic TM63 source composition and its transitive axiom audit remain unaccepted; keep this result in im-results/ until that gate passes. In particular, (3) is not an unconditional lower-bound certificate for BB(6), and it says nothing about the remaining six-state machines.
