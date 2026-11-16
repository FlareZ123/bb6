# Odd-reset level-scale bound

**Status:** exact mathematical derivation from the complete first-reset source grammar. This is a general source-level bound, not a blank-root reachability exclusion and not a BB(6) decision. Kept in `im-results/`.

## Theorem

Suppose an odd first-reset edge has source first-failure level (L), source parameter (P=2^t d), and child (u), with
[
d\ge1,\qquad 6\cdot2^L+1\le P\le8\cdot2^L-1,
\qquad 2u+5=3^{t+1}d.
]
Suppose the child has first-failure level (K\ge2), so in particular
[
4\cdot2^K\le u+K+4.
]
Then
[
\boxed{t\le L,\qquad 2^{K-2}<3^L.}
]
Equivalently, every odd reset can raise the first-failure level only to
[
K<2+L\log_2 3.
]
The power inequality is the exact integer statement; the logarithmic form is only an interpretation.

## Proof

First, (t\le L). If (t\ge L+1), then
[
P=2^t d\ge2^{L+1}d.
]
The upper source band gives (2d<8), hence (d<4). The lower source band gives
[
2d\ge6+2^{-L}>6,
]
hence (d\ge4), a contradiction.

Put (X=2u+5=3^{t+1}d). Since (P=2^td),
[
2^tX=3^{t+1}P
 <8\cdot3^{t+1}2^L
 =24\cdot3^t2^L
 \le24\cdot3^L2^t,
]
where the final inequality uses (t\le L), equivalently (3^t2^L\le3^L2^t). Dividing by (2^t) gives
[
X<24\cdot3^L. 	ag{1}
]

The child first-failure lower guard gives
[
8\cdot2^K\le2u+2K+8=X+2K+3,
]
so
[
X\ge8\cdot2^K-2K-3.
]
For (K\ge2), (2K+3\le2\cdot2^K), and therefore
[
X\ge6\cdot2^K. 	ag{2}
]
Combining (1) and (2),
[
6\cdot2^K\le X<24\cdot3^L,
]
which is exactly (2^K<4\cdot3^L), or (2^{K-2}<3^L). (square)

## Consequence for the t=1 Q-parent intersection

For a genuine t=1 Q-parent match at level (K\ge10), the existing even-entry phase exclusion in [T1-Q-PARENT-FATAL-REDUCTION.md](T1-Q-PARENT-FATAL-REDUCTION.md) says that the level-(K) entry cannot be an even child from level (K-1). It must therefore be an odd-reset child from some lower source level (L).

Applying the theorem to that incoming edge gives the additional necessary condition
[
\boxed{2^{K-2}<3^L.}
]
Thus the incoming odd parent of any surviving t=1 Q candidate cannot come from an arbitrarily low level: its source level must exceed ((K-2)\log_3 2). The incoming valuation also satisfies (t_{\rm in}\le L).

This narrows the root-facing predecessor search but does not exclude it. In particular, it is compatible with the arbitrarily deep synthetic inverse chains in [NESTED-ODD-PARENT-HENSEL.md](NESTED-ODD-PARENT-HENSEL.md). No claim is made that the source height at level (L) is root-reachable merely because it satisfies the odd-parent equations.

## Reuse

The bound is independent of the special t=1 Q equation and applies to every odd reset whose child has first-failure level at least 2. It can be used to prune exact inverse-parent searches and to bound the source level of any odd feeder of a fatal or Q-parent target.
