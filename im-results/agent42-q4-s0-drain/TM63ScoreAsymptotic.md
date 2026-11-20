# Two-term asymptotic expansion of the TM63 champion score

**Status:** new paper-level consequence of the existing exact cost decomposition. It does not certify the uncompiled authentic-root/dispatcher composition and does not establish a BB(6) upper bound.

Let
\[
S=C_{\rm root}+D_{\rm root}+D_N,\qquad
b=b_N,\qquad k=b_{N-1},
\]
where \(N\) is the outer dispatcher index, \(N\ge256\), and
\[
b_0=R,\qquad b_{j+1}=2^{b_j}-1,\qquad U\le R,\qquad R\ge63.
\]
Set
\[
\ell=\log_2(b+1).
\]
Because \(b=2^k-1\), we have \(k=\ell\) exactly. Also \(b\ge2^N R\) and \(b\ge2^R-1\), so \(N\le\ell\) and \(R\le\ell\). In particular, \(\ell\ge N\ge256\).

The exact score split and root-prefix bounds are recorded in [TM63PublishedTowerSandwich.md](TM63PublishedTowerSandwich.md). The exact dispatcher-plus-terminal cost identity is recorded in [SectionResultThreeCycle.md](SectionResultThreeCycle.md):
\[
D_N
=10N^2+37N+90+12(N+1)U
+\sum_{j=0}^{N-1}
\left(6\cdot4^{b_j}+42\cdot2^{b_j}+
(12(N-j)-9)b_j\right).
\tag{1}
\]
The exact final summand, also isolated in [DirectTerminalTetrationBound.md](../agent24-champion-time/DirectTerminalTetrationBound.md), is
\[
L_N=6\cdot4^{k}+42\cdot2^{k}+3k
=6(b+1)^2+42(b+1)+3\ell
=6b^2+54b+48+3\ell.
\tag{2}
\]
All other terms in the score split are nonnegative. Thus \(S=L_N+\Delta\), with \(\Delta\ge0\).

## Bounding the remainder after the exact final summand

Removing the \(j=N-1\) term from (1) gives the exact remainder
\[
\begin{aligned}
\Delta={}&C_{\rm root}+D_{\rm root}
+10N^2+37N+90+12(N+1)U\\
&+\sum_{j=0}^{N-2}
\left(6\cdot4^{b_j}+42\cdot2^{b_j}
+(12(N-j)-9)b_j\right).
\end{aligned}
\tag{3}
\]
The root-prefix estimates give
\[
C_{\rm root}+D_{\rm root}<\frac{133}{9}R^2<15R^2.
\tag{4}
\]
For \(j\le N-2\), monotonicity of the \(b_j\) and
\(2^{b_j}=b_{j+1}+1\) give
\[
6\cdot4^{b_j}+42\cdot2^{b_j}
=6b_{j+1}^2+54b_{j+1}+48
\le6\ell^2+54\ell+48.
\]
The sum of the remaining linear coefficients is
\[
\sum_{j=0}^{N-2}(12(N-j)-9)=6N^2-3N-3\le6N^2.
\]
Using \(U\le R\), (3) and (4) imply
\[
\Delta<
(6N+15)\ell^2+(6N^2+66N+12)\ell+10N^2+85N+90.
\tag{5}
\]
Also \(k=\ell=b_{N-1}\ge2^{N-1}R\ge2^{N-1}\), so
\(N\le1+\log_2\ell\). Put \(m=\log_2\ell\). Substitution of
\(N\le m+1\) into (5) gives
\[
\Delta<
(6m+21)\ell^2+(6m^2+78m+84)\ell
+10m^2+105m+185.
\]
For \(\ell\ge256\), \(m\ge8\), \(m\le\ell/16\), and \(\ell\ge m\).
The three terms are respectively bounded by
\(9(1+m)\ell^2\), \(84(1+m)\ell^2\), and
\((1+m)\ell^2\). Therefore
\[
\boxed{0\le\Delta<94(1+m)\ell^2<100(1+\log_2\ell)\ell^2.}
\tag{6}
\]

Consequently the exact score has the explicit two-term expansion
\[
\boxed{
S_{\rm TM1}
=6b_N^2+54b_N+48+3\ell+\Delta,
\qquad
0\le\Delta<100(1+\log_2\ell)\ell^2,\quad
\ell=\log_2(b_N+1).
}
\tag{7}
\]
In particular,
\[
54<
\frac{S_{\rm TM1}-6b_N^2}{b_N}
<
54+\frac{48+3\ell+100(1+\log_2\ell)\ell^2}{2^\ell-1}
<
54+6\times10^{-70},
\tag{8}
\]
where the final numerical inequality holds for integer \(\ell\ge256\); the displayed quotient is decreasing there and is already below \(6\times10^{-70}\) at \(\ell=256\).

The relative excess over the quadratic final-increment term is localized even more sharply:
\[
\boxed{
\frac{S_{\rm TM1}}{6(b_N+1)^2}-1
=
\frac{7}{b_N+1}+\varepsilon_N,\qquad
0<\varepsilon_N<
\frac{3\ell+100(1+\log_2\ell)\ell^2}{6(b_N+1)^2}.
}
\tag{9}
\]
Thus the score is not merely dominated by the final counted increment: after its exact quadratic and linear terms are removed, the entire remaining cost is \(O((\log b_N)^2\log\log b_N)\), with the explicit bound above.

## Evidence boundary

This derivation uses the exact symbolic dispatcher cost identity and existing root-prefix bounds. It introduces no new simulation claim and no new Lean theorem. The authentic TM63 source composition and its transitive axiom audit remain unaccepted; keep this result in im-results/ until that gate passes. It is not an unconditional lower-bound certificate for BB(6), and it says nothing about the remaining six-state machines.
