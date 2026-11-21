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


## Arbitrary-depth iterated-log expansion

The same decomposition can be peeled to any fixed depth, not only the
last two increments. First note that the authentic source parameters
satisfy \(N<R\). Indeed,
\[
A=\sum_{j=7}^{M+42}V_j<2V_{M+42}.
\]
Writing \(x=V_{M+42}\ge63\), we have
\[
N=(2^{78}-1)2^A-3<2^{2x+78},
\]
whereas \(2^x-1>2x+78\) and monotonicity of \(V\) give
\[
R=V_{M+46}=2^{V_{M+45}}-1
>2^{2x+78}-1\ge N.
\]
Thus \(N<R\).

Set
\[
u_r=b_{N-r}\quad(0\le r\le N).
\]
Then \(u_0=b_N\), \(u_1=\ell\), \(u_2=\kappa\), and
\[
u_{r-1}=2^{u_r}-1.
\]
Writing
\[
P=10N^2+37N+90+12(N+1)U,
\]
the exact score identity (1), reindexed by \(r=N-j\), is
\[
S_{\rm TM1}
=C_{\rm root}+D_{\rm root}
+P+\sum_{r=1}^{N}\left(f(u_r)+(12r-9)u_r\right).
\]
For any \(1\le p\le N\), define the nonnegative tail
\[
E_p=C_{\rm root}+D_{\rm root}+P
+\sum_{r=p+1}^{N}\left(f(u_r)+(12r-9)u_r\right).
\]
The first \(p\) increments are therefore exact:
\[
\boxed{
S_{\rm TM1}
=\sum_{r=1}^{p}
\left(
6(u_{r-1}+1)^2+42(u_{r-1}+1)+(12r-9)u_r
\right)+E_p.
}
\tag{13}
\]

There is a uniform explicit tail bound
\[
\boxed{0\le E_p<100u_p^2\qquad(1\le p\le N).}
\tag{14}
\]
To prove it, \(u_p\ge R\ge63\) and
\(u_{r-1}=2^{u_r}-1\ge2u_r\). The same inequality
\(f(x)/f(2x)<1/32\) used above shows
\[
\sum_{r=p+1}^{N}f(u_r)
<\frac{32}{31}f(u_{p+1})
=\frac{32}{31}\left(6(u_p+1)^2+42(u_p+1)\right)
<8u_p^2.
\]
Also \(\sum_{r=p+1}^{N}u_r<2u_p\), so the weighted linear tail is
\(<24Nu_p\le24u_p^2\), using \(N<R\le u_p\). The root term is
\(<15R^2\le15u_p^2\). Finally, \(N<R\le u_p\), \(U\le R\), and
\(u_p\ge63\) give
\[
10N^2+37N+90<12u_p^2,\qquad
12(N+1)U<13u_p^2.
\]
Adding these five contributions gives \(E_p<72u_p^2<100u_p^2\).

Equation (13) is an arbitrary finite-depth expansion along the
iterated-log sequence
\[
u_1=\ell,\quad
u_2=\log_2(\ell+1),\quad
u_3=\log_2(u_2+1),\quad\ldots.
\]
For each fixed \(p\), it identifies the last \(p\) dispatcher
increments exactly and leaves an error bounded by the square of the
next iterated logarithm. The earlier three-term expansion is the
\(p=2\) specialization, with the sharper bound
\(\Delta_2<100(\log_2\ell)^2\) established above.

## Evidence boundary

This derivation uses the exact symbolic dispatcher cost identity and existing root-prefix bounds. It introduces no new simulation claim and no new Lean theorem. The authentic TM63 source composition and its transitive axiom audit remain unaccepted; keep this result in im-results/ until that gate passes. It is not an unconditional lower-bound certificate for BB(6), and it says nothing about the remaining six-state machines.
