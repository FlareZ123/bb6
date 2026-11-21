# Three-term asymptotic expansion of the TM63 champion score

**Status:** new paper-level consequence of the existing exact cost decomposition. It does not certify the uncompiled authentic-root/dispatcher composition and does not establish a BB(6) upper bound.

Let
\[
S=C_{\rm root}+D_{\rm root}+D_N,\qquad
b=b_N,\qquad k=b_{N-1},
\]
where \(N\) is the outer dispatcher index, \(3\mid N\), \(N\ge256\), and
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

## Three-term expansion by peeling the last two dispatcher increments

Removing the \(j=N-1\) term from (1) gives
\[
S_{\rm TM1}=L_N+\Delta,\qquad
L_N=6(b_N+1)^2+42(b_N+1)+3\ell,
\]
where
\[
\begin{aligned}
\Delta={}&C_{\rm root}+D_{\rm root}
+10N^2+37N+90+12(N+1)U\\
&+\sum_{j=0}^{N-2}
\left(f(b_j)+(12(N-j)-9)b_j\right),\\
f(x)={}&6\cdot4^x+42\cdot2^x.
\end{aligned}
\tag{3}
\]
Put
\[
\ell=b_{N-1},\qquad \kappa=b_{N-2}=\log_2(\ell+1),
\qquad m=\log_2\ell.
\]
The last two dispatcher increments can be isolated exactly. The
\(j=N-1\) term is \(L_N\). The \(j=N-2\) term is
\[
f(\kappa)+15\kappa
=6(\ell+1)^2+42(\ell+1)+15\kappa
=6\ell^2+54\ell+48+15\kappa.
\]
Consequently
\[
\boxed{
S_{\rm TM1}
=6b_N^2+54b_N+6\ell^2+57\ell+96+15\kappa+\Delta_2,
}
\tag{4}
\]
where the remaining nonnegative contribution is exactly
\[
\begin{aligned}
\Delta_2={}&C_{\rm root}+D_{\rm root}
+10N^2+37N+90+12(N+1)U\\
&+\sum_{j=0}^{N-3}
\left(f(b_j)+(12(N-j)-9)b_j\right).
\end{aligned}
\tag{5}
\]

## Bounding the second remainder

Because \(b_0=R\ge63\) and \(b_{j+1}=2^{b_j}-1\), every update satisfies
\(b_{j+1}\ge2b_j\). In particular,
\[
\ell=b_{N-1}\ge2^{N-1}R,\qquad
\kappa=b_{N-2}\ge2^{N-2}R.
\]
Since \(N\ge256\) and \(R\ge63\), this gives
\[
m=\log_2\ell>260.
\]
Also \(N\le m+1\), \(\kappa\le m+1\), and
\[
b_{N-3}=\log_2(\kappa+1)\le m+2,\qquad
R\le\frac{m+1}{2^{N-2}}\le m+1.
\]

For \(x\ge3\),
\[
f(x)\le\frac{45}{4}4^x,\qquad
f(2x)\ge6\cdot16^x,
\]
so
\[
\frac{f(x)}{f(2x)}
\le\frac{15}{8\cdot4^x}
\le\frac{15}{512}<\frac1{32}.
\]
It follows that
\[
\sum_{j=0}^{N-3}f(b_j)
<\frac{32}{31}f(b_{N-3}).
\]
As \(2^{b_{N-3}}=\kappa+1\),
\[
f(b_{N-3})=6(\kappa+1)^2+42(\kappa+1)
\le6(m+2)^2+42(m+2)<7m^2.
\]
Thus
\[
\sum_{j=0}^{N-3}f(b_j)<8m^2.
\tag{6}
\]

For the linear terms, \(b_{j+1}\ge2b_j\) gives
\[
\sum_{j=0}^{N-3}b_j<2b_{N-3}.
\]
The coefficients are at most \(12N\), hence
\[
\sum_{j=0}^{N-3}(12(N-j)-9)b_j
<24N b_{N-3}
\le24(m+1)(m+2)<25m^2.
\tag{7}
\]

The root term uses the existing exact bound
\(C_{\rm root}+D_{\rm root}<15R^2\). Since \(R\le m+1\),
\[
C_{\rm root}+D_{\rm root}<15(m+1)^2<16m^2.
\tag{8}
\]
The remaining polynomial terms satisfy
\[
10N^2+37N+90
\le10(m+1)^2+37(m+1)+90<20m^2,
\tag{9}
\]
and, since \(U\le R\),
\[
12(N+1)U
\le12(m+2)(m+1)<13m^2.
\tag{10}
\]
All inequalities above hold for \(m>260\). Combining (6)--(10),
\[
\boxed{0\le\Delta_2<82m^2<100m^2.}
\tag{11}
\]

The resulting three-term asymptotic expansion is therefore
\[
\boxed{
\begin{aligned}
S_{\rm TM1}
={}&6b_N^2+54b_N+6\ell^2+57\ell+96\\
&+15\log_2(\ell+1)+\Delta_2,\\
&0\le\Delta_2<100(\log_2\ell)^2.
\end{aligned}
}
\tag{12}
\]
Thus, after the exact leading quadratic and linear terms in \(b_N\),
the next contribution is explicitly \(6\ell^2+57\ell+O(\log\ell)\),
and the remaining uncertainty is only
\(O((\log_2\ell)^2)=O((\log_2\log_2 b_N)^2)\).
This is substantially sharper than merely bounding the entire
pre-final dispatcher remainder by \(O(\ell^2)\).

As a coarser corollary, (12) also implies the earlier bound
\(\Delta<\tfrac{13}{2}\ell^2\) for the one-term remainder in (3);
the three-term formula (12) is the stronger statement.


## Evidence boundary

This derivation uses the exact symbolic dispatcher cost identity and existing root-prefix bounds. It introduces no new simulation claim and no new Lean theorem. The authentic TM63 source composition and its transitive axiom audit remain unaccepted; keep this result in im-results/ until that gate passes. It is not an unconditional lower-bound certificate for BB(6), and it says nothing about the remaining six-state machines.
