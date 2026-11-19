# The #623 root recurrence as a perturbed tent map

**Agent 3, 2026-11-19. Status: exact algebraic reduction; not an all-time root proof.**

This note reorganizes the source-derived root gap/scale cocycle into a one-dimensional normalized map. The useful feature is that the denominator coordinate \(S=a+d\) has a branch-independent exact update, while the halting window becomes a shrinking neighborhood of a single critical ratio \(1/5\).

The derivation uses the exact canonical-ray residuals in [Agent 41's drain valuation normal form](agent41-623-3euclidean/DrainValuationNormalForm.md) and the source gap/scale cocycle in [Agent 1's root-ray analysis](agent1-machine623-3euclidean-correction-bounds/RootRayGapCocycle.md). It does not introduce a substitute simulator.

## 1. Exact two-coordinate recurrence

For a section state \(D(a,d)\), put
\[
q=\min(a,d),\qquad p=|a-d|,\qquad g=p-3q,\qquad S=p+2q=a+d.
\]
Let \((\beta,\delta)\) be the exact source-derived canonical-ray residuals for the current input sector. The source cocycle gives:

- if the output is left-oriented,
  \[
  g'=g-9q+\beta-4\delta,\qquad q'=3q+\delta;
  \]
- if the output is right-oriented,
  \[
  g'=-4g-9q+\delta-4\beta,\qquad q'=p+\beta.
  \]

Since \(p'=g'+3q'\), these identities are equivalently
\[
(p',q')=
\begin{cases}
(p-3q+\beta-\delta,\;3q+\delta),&\mathsf L,\\
(3q-p+\delta-\beta,\;p+\beta),&\mathsf R.
\end{cases}
\tag{1}
\]

A useful cancellation occurs in the linear form \(S=p+2q\). In **both** output cases,
\[
\boxed{S'=p'+2q'=p+3q+\beta+\delta=S+q+\beta+\delta.}
\tag{2}
\]
Thus the leading scale update is independent of the output orientation.

## 2. The source correction is a positive digit statistic

Let \(\ell\) be the parity-adjusted ternary depth of the canonical drain input \(b\), and let \(n_1,n_2\) be the counts of ternary digits equal to 1 and 2 in
\[
N=\frac{2b-1+3^\ell}{4}.
\]
Write \(R=n_1+n_2\), \(e=n_2\), and \(D=\ell-2e\), as in the drain valuation normal form. Then
\[
D+2R=\ell+2n_1.
\tag{3}
\]

The exact residuals from that normal form give the following values of \(\beta+\delta\):

| Input sector | \(\beta\) | \(\delta\) | \(\beta+\delta\) |
|---|---:|---:|---:|
| LO | \(-D-5\) | \(2D+2R+14\) | \(D+2R+9=\ell+2n_1+9\) |
| LE | \(-D-2\) | \(2D+2R+8\) | \(D+2R+6=\ell+2n_1+6\) |
| RO | \(4-D\) | \(2D+2R\) | \(D+2R+4=\ell+2n_1+4\) |
| RE | \(1-D\) | \(2D+2R+3\) | \(D+2R+4=\ell+2n_1+4\) |

Consequently, for every positive canonical drain input,
\[
\boxed{S'=S+q+\ell+2n_1+c_\Sigma,\qquad
c_\Sigma\in\{9,6,4,4\}.}
\tag{4}
\]
In particular, \(S\) strictly increases, with a source-exact increment containing the nonnegative digit statistic \(\ell+2n_1\). This is stronger and more structured than a uniform additive mass-growth estimate. It does not by itself imply nonhalting.

The same digit formulas give coarse bounds
\[
|\beta|\le \ell+5,\qquad 0\le\delta\le4\ell+14,
\qquad |T|\le5\ell+19,
\]
where \(T=\delta-\beta\) is the output-side threshold. Since \(\ell=O(\log(q+3))\), all corrections are logarithmic in the root scale. The threshold constants in LO/LE/RO/RE are respectively \(19,10,-4,2\), so \(T=3D+2R+c_T\).

## 3. Exact normalized map and its ideal limit

For \(S>0\), define
\[
r=\frac qS\in[0,1/2].
\]
Using (1) and (2), the exact update is
\[
r'=
\begin{cases}
\displaystyle\frac{3q+\delta}{S+q+\beta+\delta},
&\mathsf L,\\[1.2ex]
\displaystyle\frac{S-2q+\beta}{S+q+\beta+\delta},
&\mathsf R.
\end{cases}
\tag{5}
\]
Equivalently,
\[
r'=
\begin{cases}
\displaystyle\frac{3r+\delta/S}{1+r+(\beta+\delta)/S},&\mathsf L,\\[1.2ex]
\displaystyle\frac{1-2r+\beta/S}{1+r+(\beta+\delta)/S},&\mathsf R.
\end{cases}
\tag{6}
\]

The source comparison selecting the output side is \(g\ge T\) for left output and \(g<T\) for right output. Since \(g=S-5q\), this is
\[
\mathsf L\quad\Longleftrightarrow\quad
r\le\frac15-\frac{T}{5S}.
\tag{7}
\]
The branch boundary is therefore \(1/5+O(\log S/S)\).

If the logarithmic source corrections are suppressed, (6) becomes the piecewise map
\[
f(r)=
\begin{cases}
\displaystyle\frac{3r}{1+r},&0\le r\le1/5,\\[1.2ex]
\displaystyle\frac{1-2r}{1+r},&1/5<r\le1/2.
\end{cases}
\tag{8}
\]
Both branches map their respective intervals onto \([0,1/2]\). They meet at the critical point:
\[
f(1/5)=1/2,\qquad f(1/2)=0,\qquad f(0)=0.
\]
The one-sided derivatives at \(1/5\) are \(+25/12\) and \(-25/12\). Thus (8) is a full-branch expanding tent-like map, with a particularly simple critical orbit
\[
1/5\longmapsto1/2\longmapsto0\longmapsto0.
\]

Equations (5)--(7) show that the actual #623 root follows a logarithmically small \(O(\log S/S)\) perturbation of this map. The perturbation is not arbitrary: its denominator correction is the positive digit statistic in (4), while \(\beta\), \(\delta\), and \(T\) are explicit functions of the ternary digit counts.

## 4. A branch-independent quadratic cocycle and the 3-Euclidean conjugacy

The ideal gap map has the common quadratic form
\[
Q(p,q)=p^2+3pq+3q^2.
\]
The exact corrected map retains a branch-independent quadratic update. Set
\[
x=p-3q+\beta-\delta,\qquad y=3q+\delta.
\]
The left output is \((p',q')=(x,y)\), while the right output is exactly \((p',q')=(-x,x+y)\). The involution \(U(x,y)=(-x,x+y)\) preserves \(Q\). Expanding \(Q(x,y)\) therefore gives, for either output branch,
\[
\boxed{
Q'=Q+6q^2+(2\beta+\delta)g
+9q(\beta+\delta)+\beta^2+\beta\delta+\delta^2.
}
\tag{10}
\]

With \(R=n_1+n_2\), the two correction combinations are
\[
\eta:=\beta+\delta=\ell+2n_1+c_\eta,\qquad
\sigma:=2\beta+\delta=2R+c_\sigma,
\]
where
\[
(c_\eta,c_\sigma)=
\begin{cases}
(9,4)&\mathrm{LO},\\
(6,4)&\mathrm{LE},\\
(4,8)&\mathrm{RO},\\
(4,5)&\mathrm{RE}.
\end{cases}
\]
Hence
\[
Q'=Q+6q^2+\sigma g+9q\eta+
\underbrace{(\beta^2+\beta\delta+\delta^2)}_{\ge0}.
\tag{11}
\]
The ideal common gain \(6q^2\) is accompanied by the positive term \(9q\eta\) and a positive-definite quadratic correction. The only sign-indefinite term is \(\sigma g\). Inside the source-supported preterminal window, \(|g|=O(\ell)\) and \(\sigma=O(\ell)\), so this term is \(O(\ell^2)\), whereas \(6q^2+9q\eta\) dominates for sufficiently large \(q\). Thus \(Q\) strictly increases at every sufficiently large preterminal-window state; this does not exclude such a state.

The quadratic form is related to the normalized ratio by
\[
Q=S^2(1-\rho+\rho^2),\qquad
\boxed{25Q-21S^2=(p-3q)(4p+3q)=g(4p+3q).}
\tag{12}
\]
The critical ratio \(\rho=1/5\) is exactly the quadratic level \(Q/S^2=21/25\). Since \(4p+3q\) is comparable to \(S\) for \(p,q\ge0\), the source window \(|g|=O(\log S)\) is equivalently
\[
|25Q-21S^2|=O(S\log S).
\]

For \(q>0\), put \(u=g/q\). Then \(\rho=1/(u+5)\), and the ideal map (8) becomes
\[
u'=
\begin{cases}
(u-9)/3,&u>0,\\
(-4u-9)/(u+3),&u<0.
\end{cases}
\tag{13}
\]
This is exactly the 3-Euclidean projective map in the existing root-gap analysis. Its two preimages of \(u=0\) are \(u=9\) and \(u=-9/4\), the two previously identified cancellation centres. In the \(\rho\) coordinate they are \(1/14\) and \(4/11\), the two inverse images of \(1/5\) under (8). Thus the tent-map critical point, the cancellation centres, and the source-supported preterminal ratio-four window describe the same projective geometry.

For the exact source map, the branch boundary is \(g=T\), or \(u=T/q=O(\ell/q)\), rather than exactly zero. The exact digit corrections in (10)--(11) remain the obstacle to an all-time avoidance theorem.

## 5. Terminality forces the preceding root state into the critical window

The four source-certified TerminalRatio4 theorems apply when the output of a canonical drain is terminal. They therefore constrain the **input state of that drain**: the preceding state on the authentic root orbit, not the terminal output state itself.

Write that predecessor as \(D(a,d)\), with the same \(p,q,g,S\) as above. The four TerminalRatio4 inequalities translate directly into bounds on \(g\):

| Input sector | TerminalRatio4 inequality | Bound on \(|g|\), using \(K=n+6\) |
|---|---|---:|
| LO (odd far-left) | \(|4d-a|\le K+5n+29\) | \(6n+35\) |
| LE (even far-left) | \(|4d-a|\le K+5n+20\) | \(6n+26\) |
| RO (odd near-right) | \(|4a-d|\le K+5n+12\) | \(6n+18\) |
| RE (even near-right) | \(|4a-d|\le K+8n+17\) | \(9n+23\) |

For LO/LE, \(g=a-4d\). For RO/RE, \(g=d-4a\). Thus every terminal output forces its predecessor into
\[
|g|\le9n+23.
\]
Here \(n\le\ell\le n+1\), and \(\ell=O(\log(q+3))\). Since \(g=S-5q\), a terminal successor requires its preceding root state to satisfy
\[
\boxed{\left|\rho-\frac15\right|
\le\frac{9n+23}{5S}
=O(\log S/S).}
\tag{14}
\]

This is a **preterminal** critical-window condition: it is the predecessor state that must approach \(\rho=1/5\), not the terminal output state. The first exceptional transition is \(D(0,7)\to D(6,14)\); from there the regular canonical-ray recurrence applies.

The open root problem is therefore precise:

> Prove that no state on the authentic blank-root orbit after the exceptional prefix enters the source-supported shrinking window (14). This would rule out every terminal successor.

The exact branch-selection boundary (7) lies at \(1/5+O(\log S/S)\) as well. Thus the same critical region controls both the output-side switch and the only source-certified predecessor region from which a terminal successor can arise.

The critical point is preperiodic under the ideal map:
\[
1/5\longmapsto1/2\longmapsto0\longmapsto0.
\]
A proof might exploit the exact ternary digit-statistic corrections to rule out the corresponding short itineraries, or establish a uniform symbolic/Diophantine separation from the critical point.

**Limitations.** The normalized map, quadratic cocycle, and translation of the four TerminalRatio4 inequalities are algebraic consequences of the existing source cocycle and source-certified ratio bounds. No uniform critical-window avoidance theorem is proved here; no new root state is classified; and machine #623 remains unresolved. The note belongs in \`im-results/\`, not \`results/\`.
