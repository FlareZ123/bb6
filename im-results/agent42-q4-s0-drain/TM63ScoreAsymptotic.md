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
=6(b+1)^2+42(b+1)+3k
=6b^2+54b+48+3k.
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
\le6k^2+54k+48.
\]
The sum of the remaining linear coefficients is
\[
\sum_{j=0}^{N-2}(12(N-j)-9)=6N^2-3N-3\le6N^2.
\]
Using \(U\le R\), (3) and (4) therefore imply
\[
\Delta<
15R^2+10N^2+85N+90+12(N+1)R
+6Nk^2+54Nk+6N^2k.
\tag{5}
\]

We next bound all three parameters by \(b^{1/16}\). Since
\(b\ge2^N R\), \(N\ge256\), and \(N^{16}\le2^N\) for \(N\ge256\),
\[
N\le b^{1/16}.
\]
If \(R\le256\), then \(b\ge2^{256}\), so \(R\le b^{1/16}\); if
\(R\ge257\), use \(b\ge2^R-1\ge R^{16}\). The same split applies to
\(k\): if \(k\le256\), use \(b\ge2^{256}\); if \(k\ge257\), use
\(b=2^k-1\ge k^{16}\). The elementary inequalities
\(x^{16}\le2^x-1\) for integer \(x\ge257\) follow at \(257\) and
then by monotonicity of \(2^x/x^{16}\). Hence
\[
N,R,k\le b^{1/16}.
\tag{6}
\]
Substituting (6) into (5), and using \(b\ge1\), gives
\[
\Delta<
(15+10+85+90+24+6+54+6)b^{3/16}
=290b^{3/16}<300b^{3/16}.
\]
Consequently the exact score lies in the narrow interval
\[
\boxed{
6(b_N+1)^2+42(b_N+1)+3b_{N-1}
\le S_{\rm TM1}
<
6(b_N+1)^2+42(b_N+1)+3b_{N-1}
+300b_N^{3/16}.
}
\tag{7}
\]
Equivalently,
\[
S_{\rm TM1}
=6b_N^2+54b_N+48+3b_{N-1}+\Delta,
\qquad 0\le\Delta<300b_N^{3/16}.
\tag{8}
\]
In particular, the normalized linear correction is pinned to \(54\):
\[
54<
\frac{S_{\rm TM1}-6b_N^2}{b_N}
<
54+351b_N^{-13/16}
<
54+9\times10^{-61},
\tag{9}
\]
where the final numerical inequality uses \(b_N\ge2^{256}\).

The relative excess over the quadratic term is also sharply localized:
\[
\frac{7}{b_N+1}
<
\frac{S_{\rm TM1}}{6(b_N+1)^2}-1
<
\frac{7.01}{b_N}.
\tag{10}
\]
For the upper inequality, use \(k\le b^{1/16}\),
\(\Delta<300b^{3/16}\), and \(b\ge2^{256}\) to obtain
\(42+3b^{1/16}+300b^{3/16}<0.06b\).

Thus the score is not merely dominated by the final counted increment: after its exact quadratic and linear terms are removed, the entire remaining cost is less than \(300b_N^{3/16}\). This is a two-term asymptotic expansion with an explicit sublinear error, conditional on the existing source-cost identities.

## Evidence boundary

This derivation uses the exact symbolic dispatcher cost identity and existing root-prefix bounds. It introduces no new simulation claim and no new Lean theorem. The authentic TM63 source composition and its transitive axiom audit remain unaccepted; keep this result in im-results/ until that gate passes. It is not an unconditional lower-bound certificate for BB(6), and it says nothing about the remaining six-state machines.
