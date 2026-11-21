# Two-term asymptotic expansion of the TM63 champion score

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

## Geometric remainder bound after the exact final summand

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

The earlier estimate bounded each quadratic summand by the final one and
paid a factor \(N\). The recurrence makes that unnecessary: because
\(b_0=R\ge63\) and \(b_{j+1}=2^{b_j}-1\), we have
\(b_{j+1}\ge2b_j\) for every \(j\). Put
\[
f(x)=6\cdot4^x+42\cdot2^x.
\]
For \(x\ge3\),
\[
f(x)\le\frac{45}{4}4^x,\qquad
f(2x)\ge6\cdot16^x,
\]
and hence
\[
\frac{f(x)}{f(2x)}
\le\frac{15}{8\cdot4^x}
\le\frac{15}{512}<\frac1{32}.
\]
Thus \(f(b_j)<f(b_{j+1})/32\), and the entire pre-final quadratic sum
is geometrically dominated:
\[
\sum_{j=0}^{N-2}f(b_j)
<\frac{32}{31}f(b_{N-2}).
\]
Since \(2^{b_{N-2}}=b_{N-1}+1=\ell+1\),
\[
f(b_{N-2})=6(\ell+1)^2+42(\ell+1)
=6\ell^2+54\ell+48.
\]
For \(\ell\ge256\), \(54/\ell+48/\ell^2<1/4\), so
\[
\boxed{\sum_{j=0}^{N-2}f(b_j)
<\frac{200}{31}\ell^2<\frac{13}{2}\ell^2.}
\tag{4}
\]

The linear sum is also dominated by its last counter. From
\(b_{j+1}\ge2b_j\),
\[
\sum_{j=0}^{N-2}b_j<2b_{N-2}.
\]
Writing \(m=\log_2\ell\), we have
\(b_{N-2}=\log_2(\ell+1)\le m+1\) and \(N\le m+1\). Therefore
\[
\begin{aligned}
\sum_{j=0}^{N-2}(12(N-j)-9)b_j
&<24N b_{N-2}\\
&\le24(m+1)^2
\le\frac{\ell^2}{16},
\end{aligned}
\tag{5}
\]
where the last inequality holds for \(m\ge8\).

The root contribution can be sharpened using the exact all-ones drain
rather than its previous coarse comparison with \(R^2\). The existing
root-prefix bound gives \(C_{\rm root}<R^2\). With
\(R=2^{n-1}-1\), the exact drain identity gives
\[
D_{\rm root}=\operatorname{drainCost}(R,0)
=6\cdot4^{n-1}+42\cdot2^{n-1}-12n-36.
\]
For the authentic \(n\ge7\),
\[
7R^2-D_{\rm root}
=4^{n-1}-28\cdot2^n+12n+43>0,
\]
since \(4^{n-1}\ge32\cdot2^n\). Consequently
\[
\boxed{C_{\rm root}+D_{\rm root}<8R^2\le8\ell^2.}
\tag{6}
\]

Finally, using \(N\le m+1\) and \(U\le R\le\ell\), the remaining
polynomial terms satisfy
\[
10N^2+37N+90\le20m^2\le\frac{\ell^2}{32},
\]
and
\[
12(N+1)U\le12(m+2)\ell\le\frac{\ell^2}{2}
\]
for \(m\ge8\). Their sum is therefore below \(17\ell^2/32<\ell^2\).
Combining this with (4)--(6) yields
\[
\Delta<
\left(8+\frac{13}{2}+\frac1{16}+\frac{17}{32}\right)\ell^2
=\frac{483}{32}\ell^2
<16\ell^2.
\]
Thus the stronger explicit remainder estimate is
\[
\boxed{0\le\Delta<16\ell^2.}
\tag{7}
\]

The exact score consequently has the quadratic-error expansion
\[
\boxed{
S_{\rm TM1}
=6b_N^2+54b_N+48+3\ell+\Delta,\qquad
0\le\Delta<16\ell^2,\quad
\ell=\log_2(b_N+1).
}
\tag{8}
\]
In particular,
\[
54<
\frac{S_{\rm TM1}-6b_N^2}{b_N}
<
54+\frac{48+3\ell+16\ell^2}{2^\ell-1}
<
54+6\times10^{-71},
\tag{9}
\]
where the final numerical bound remains valid for integer
\(\ell\ge256\).

Likewise, the relative excess over the quadratic final-increment term is
\[
\boxed{
\frac{S_{\rm TM1}}{6(b_N+1)^2}-1
=
\frac{7}{b_N+1}+\varepsilon_N,\qquad
0<\varepsilon_N<
\frac{3\ell+16\ell^2}{6(b_N+1)^2}
<8\times10^{-149}.
}
\tag{10}
\]
The last numerical bound is inherited from the weaker previous estimate.
The substantive improvement is that the full remainder is now
\(O(\ell^2)=O((\log b_N)^2)\), rather than
\(O(\ell^2\log\ell)\): the pre-final quadratic costs are geometrically
dominated by the final pre-final increment, not by \(N\) copies of it.

## Evidence boundary

This derivation uses the exact symbolic dispatcher cost identity and existing root-prefix bounds. It introduces no new simulation claim and no new Lean theorem. The authentic TM63 source composition and its transitive axiom audit remain unaccepted; keep this result in im-results/ until that gate passes. It is not an unconditional lower-bound certificate for BB(6), and it says nothing about the remaining six-state machines.
