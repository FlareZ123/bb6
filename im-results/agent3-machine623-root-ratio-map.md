# The #623 root recurrence as a perturbed tent map

**Agent 3, 2026-11-19. Status: exact algebraic reduction; not an all-time root proof.**

This note reorganizes the source-derived root gap/scale cocycle into a one-dimensional normalized map. The useful feature is that the denominator coordinate (S=a+d) has a branch-independent exact update, while the halting window becomes a shrinking neighborhood of a single critical ratio (1/5).

The derivation uses the exact canonical-ray residuals in [Agent 41's drain valuation normal form](agent41-623-3euclidean/DrainValuationNormalForm.md) and the source gap/scale cocycle in [Agent 1's root-ray analysis](agent1-machine623-3euclidean-correction-bounds/RootRayGapCocycle.md). It does not introduce a substitute simulator.

## 1. Exact two-coordinate recurrence

For a section state (D(a,d)), put
[
q=\min(a,d),\qquad p=|a-d|,\qquad g=p-3q,\qquad S=p+2q=a+d.
]
Let ((\beta,\delta)) be the exact source-derived canonical-ray residuals for the current input sector. The source cocycle gives:

- if the output is left-oriented,
  [
  g'=g-9q+\beta-4\delta,\qquad q'=3q+\delta;
  ]
- if the output is right-oriented,
  [
  g'=-4g-9q+\delta-4\beta,\qquad q'=p+\beta.
  ]

Since (p'=g'+3q'), these identities are equivalently
[
(p',q')=
\begin{cases}
(p-3q+\beta-\delta,\;3q+\delta),&L,\\
(3q-p+\delta-\beta,\;p+\beta),&R.
\end{cases}
	ag{1}
]

A useful cancellation occurs in the linear form (S=p+2q). In **both** output cases,
[
oxed{S'=p'+2q'=p+3q+\beta+\delta=S+q+\beta+\delta.}
	ag{2}
]
Thus the leading scale update is independent of the output orientation.

## 2. The source correction is a positive digit statistic

Let (L) be the parity-adjusted ternary depth of the canonical drain input (b), and let (n_1,n_2) be the counts of ternary digits equal to 1 and 2 in
[
N=\frac{2b-1+3^L}{4}.
]
Write (R=n_1+n_2), (e=n_2), and (D=\\ell-2e), as in the drain valuation normal form. Then
[
D+2R=\\ell+2n_1.
	ag{3}
]

The exact residuals from that normal form give the following values of (\beta+\delta):

| Input sector | (\beta) | (\delta) | (\beta+\delta) |
|---|---:|---:|---:|
| LO | (-D-5) | (2D+2R+14) | (D+2R+9=\\ell+2n_1+9) |
| LE | (-D-2) | (2D+2R+8) | (D+2R+6=\\ell+2n_1+6) |
| RO | (4-D) | (2D+2R) | (D+2R+4=\\ell+2n_1+4) |
| RE | (1-D) | (2D+2R+3) | (D+2R+4=L+2n_1+4) |

Consequently, for every positive canonical drain input,
[
oxed{S'=S+q+L+2n_1+c_s,\qquad c_s\in\{9,6,4,4\}.}
	ag{4}
]
In particular, (S) strictly increases, with a source-exact increment that contains the nonnegative digit statistic (L+2n_1). This is stronger and more structured than a uniform additive mass-growth estimate. It does not by itself imply nonhalting.

The same digit formulas give coarse bounds
[
|\beta|\le L+5,\qquad 0\le\delta\le4L+14,
\qquad |T|\le5L+19,
]
where (T=\delta-\beta) is the output-side threshold. Since (L=O(\log(q+3))), all corrections are logarithmic in the root scale.

## 3. Exact normalized map and its ideal limit

For (S>0), define
[
r=\frac qS\in[0,1/2].
]
Using (1) and (2), the exact update is
[
r'=
\begin{cases}
\displaystyle\frac{3q+\delta}{S+q+\beta+\delta},
&L,\\[1.2ex]
\displaystyle\frac{S-2q+\beta}{S+q+\beta+\delta},
&R.
\end{cases}
	ag{5}
]
Equivalently,
[
r'=
\begin{cases}
\displaystyle\frac{3r+\delta/S}{1+r+(\beta+\delta)/S},&L,\\[1.2ex]
\displaystyle\frac{1-2r+\beta/S}{1+r+(\beta+\delta)/S},&R.
\end{cases}
	ag{6}
]

The source comparison selecting the output side is (g\ge T) for left output and (g<T) for right output. Since (g=S-5q), this is
[
L\quad\Longleftrightarrow\quad
r\le\frac15-\frac{T}{5S}.
	ag{7}
]
The branch boundary is therefore (1/5+O(\log S/S)).

If the logarithmic source corrections are suppressed, (6) becomes the piecewise map
[
f(r)=
\begin{cases}
\displaystyle\frac{3r}{1+r},&0\le r\le1/5,\\[1.2ex]
\displaystyle\frac{1-2r}{1+r},&1/5<r\le1/2.
\end{cases}
	ag{8}
]
Both branches map their respective intervals onto ([0,1/2]). They meet at the critical point:
[
f(1/5)=1/2,\qquad f(1/2)=0,\qquad f(0)=0.
]
The one-sided derivatives at (1/5) are (+25/12) and (-25/12). Thus (8) is a full-branch expanding tent-like map, with a particularly simple critical orbit
[
1/5\longmapsto1/2\longmapsto0\longmapsto0.
]

Equations (5)--(7) show that the actual #623 root follows a logarithmically small (O(\log S/S)) perturbation of this map. The perturbation is not arbitrary: its denominator correction is the positive digit statistic in (4), while (\beta), (\delta), and (T) are explicit functions of the ternary digit counts.

## 4. The halting obstruction becomes a critical-window avoidance problem

The source terminal conditions in the four canonical sectors are precisely logarithmic-width conditions on (g=p-3q), up to fixed sector offsets (9, 5, 1, or 2). In particular, a terminal hit requires
[
|S-5q|=|g|=O(\log S),
]
so
[
\boxed{|r-1/5|=O(\log S/S).}
	ag{9}
]
The open root problem can therefore be stated as follows:

> Prove that the exact digit-statistic perturbation of (8), starting from the authentic blank-root state (D(0,7)) and after its finite exceptional prefix, never enters the shrinking critical window (9).

This is a sharper dynamical formulation of the root-gap problem. The critical point is preperiodic under the ideal map, so a close visit forces a characteristic short itinerary near (1/5\to1/2\to0). A proof might exploit the exact ternary digit-statistic corrections to rule out such itineraries, or establish a uniform symbolic/Diophantine separation from the critical point.

**Limitations.** The map reduction, positive scale increment, and critical-window equivalence are algebraic consequences of the existing source cocycle and digit-statistic formulas. No uniform critical-window avoidance theorem is proved here; no new root state is classified; and machine #623 remains unresolved. The note belongs in `im-results/`, not `results/`.
