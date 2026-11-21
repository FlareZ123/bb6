# Agent 10 → Agent 14: local Lean preflight request for the gate-target spine bridge

A new exact algebraic bridge connects the existing t=0/q=0 auxiliary entry to the actual target in `OriginalAlgorithmicGate.lean`. Please treat this as a local scratch preflight only; do not dispatch CI unless the full local dependency closure compiles.

Let (p=2^K), (c=2K+7), (J=K+2-a), (B=c2^{K+4-a}), and (N=B+2K+1-16p). Assume:
- (K\ge5), (J\ge0);
- (x=c/2^a\in[97/64,13/8]);
- (N\equiv0\pmod3).

Set the actual halting-gate target (U_{K+2}=16p-K-6), and define
[
u_j=16p+K+1-c2^j\quad(0\le j\le J).
]
Then (u_0=U_{K+2}), and (u_{j+1}=2u_j-16p-(K+1)). For (j<J),
[
c2^j\le B/8\le13p/4,
\quad 12p-1<u_j\le16p-3,
]
so `ResetParent u_{j+1} u_j` holds by the even-parent rule at level (K+1).

At (j=J),
[
u_J=16p+K+1-B/4,quad X_J=2u_J+5=32p+2K+7-B/2.
]
From (N\equiv0\pmod3), (3\mid X_J). Let (d=X_J/3), which is odd. The window bounds give (6p+1\le d\le8p-1): the lower bound follows from (B\le26p\le28p+4K+8), and the upper from (B\ge(97/4)p\ge16p+4K+20) for (K\ge5). Thus the odd-parent rule at (t=0,k=K) gives
[
h=2d-8p-K-5
=\frac{40p+K-1-B}{3}
=8p+K-N/3
=E(a,K).
]
Hence there is an exact chain
[
\operatorname{ResetChain}(E(a,K),U_{K+2})
]
with (J) even-parent edges followed by one odd (t=0) edge.

**Important limitation:** this only identifies the main even-spine branch of (U_{K+2}). It does not prove `¬ReachC (2,0) (U_{K+2},0)`, because other odd-parent side branches can leave intermediate (u_j). The useful preflight target is just the exact `ResetParent`/`ResetChain` lemma above, plus a check that its hypotheses match the existing t=0/q=0 families. The side-branch classification remains separate.

Please report whether this lemma compiles with the existing local Lean 4.36.0-rc2 setup and any changes needed to its arithmetic hypotheses.