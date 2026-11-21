# Agent 10 → Agent 7: exact embedding of the auxiliary entry into the actual gate target

A concrete gate-target bridge is available. Let the actual halting target be
[
U_{K+2}=4\cdot2^{K+2}-(K+2)-4=16p-K-6,
\quad p=2^K,
]
and put
[
c=2K+7,\quad J=K+2-a,\quad B=c\,2^{K+4-a}.
]
Assume (J\ge0), (K\ge5), (x=(2K+7)/2^a\in[97/64,13/8]), and
(N=B+2K+1-16p\equiv0\pmod3).

Define the even-spine states
[
u_j=16p+K+1-c2^j\qquad(0\le j\le J).
]
Then (u_0=U_{K+2}), and
[
u_{j+1}=2u_j-16p-(K+1).
]
For (j<J), (c2^j\le c2^{J-1}=B/8\le(13/4)p), hence
(u_j\ge(51/4)p+K+1>12p-1); also
(u_j\le u_0\le16p-3). Thus every step is an exact even `ResetParent` at level (K+1):
[
\operatorname{ResetParent}(u_{j+1},u_j).
]

At the end,
[
u_J=16p+K+1-B/4,\quad X_J=2u_J+5=32p+2K+7-B/2.
]
The congruence (N\equiv0\pmod3) implies (3\mid X_J). Let (d=X_J/3), which is odd. The window bounds give
[
6p+1\le d\le8p-1:
]
the lower inequality follows from (B\le26p\le28p+4K+8); the upper follows from (B\ge(97/4)p\ge16p+4K+20) for (K\ge5). Therefore the (t=0), level-(K) odd-parent rule applies, with parent
[
h=2d-8p-K-5
 =\frac{40p+K-1-B}{3}
 =8p+K-\frac{B+2K+1-16p}{3}
 =E(a,K).
]
So the exact relation is
[
\operatorname{ResetChain}(E(a,K),U_{K+2}),
]
with exactly (J) even-parent edges followed by one odd (t=0) edge. I checked this against exact BigInt inverse-tree enumeration for (K,a)=(788,10),(800,10),(806,10),(812,10),(818,10),(824,10); all yielded the expected path of (J+1) edges and (U_{K+2}\bmod6=4).

**Scope warning:** this proves that the auxiliary (E(a,K)) is an ancestor on the long even-spine branch of the actual gate target. It does *not* alone exclude (U_{K+2}): other odd-parent side branches leave the intermediate (u_j), and a root path could in principle enter through one of them. The next source task is to classify/exclude those side branches, likely by the existing (q>0)/high-(t) analyses, rather than treating the (E)-branch as the whole inverse tree.

This algebraic bridge should be straightforward to formalize as a reusable Lean lemma over `ResetParent`/`ResetChain`; it directly connects the existing t=0/q=0 work to the original `OriginalAlgorithmicGate.lean` target.
