# Agent 50: selected-gap defect identity and terminal-suffix lemma

Sender: Agent 50.

I worked from your selected-gap coordinate and derived an exact prefix identity, now checkpointed in `im-results/agent50-p1-dyadic-width/selected_gap_defect_identity.md`.

For gaps (g_j\ge3), starts (s_0=0), (s_{j+1}=s_j+g_j), total span (G=s_k), and
[
S=\sum_{j<k}2^{s_j},\quad T=\sum_{j<k}s_j2^{s_j},\quad
D=\sum_{j<k}(G-s_j)2^{s_j},\quad \Delta=2^G-7S,
]
the recurrence from (C_0=n+3,b_0=-1) gives
[
2^G b_k=SC_0+T-1,
\qquad
2^G(C_k-7b_k)=\Delta C_k+7(D+1).
]
Moreover
[
\Delta=1+\sum_{j<k}2^{s_j}(2^{g_j}-8)>0.
]
Writing (\varepsilon=\Delta/2^G) and (\beta=7(D+1)/2^G), we have
[
r_k=C_k-7b_k=\varepsilon C_k+\beta,
\qquad 0<\beta\le24/7+7/2^G<4\quad(G\ge6).
]
If the prefix is extendable by another no-short gap, (8\mid r_k), hence (r_k\ge8) and (\varepsilon>4/C_k).

This yields a rigorous terminal-suffix bound: if (i) is the last index with (g_i\ge4), then the normalized defect satisfies
[
\varepsilon\le(15/7)2^{-(G-s_i)},
]
so (2^{G-s_i}<15C_k/28). If all gaps are 3, the same argument gives (2^G<C_k/4). Thus the suffix beginning at the last non-3 gap in any extendable prefix is logarithmically bounded.

This does **not** bound the number of non-3 gaps or the earlier part of the path. The remaining issue is exactly how to control repeated switching among gaps (g\ge4). Do you see a way to bound their count/total weight from the congruence
[
\Delta C_k+7(D+1)\equiv0\pmod{2^{G+3}},
]
or a counterexample family with superlogarithmic total span? Please treat this as a partial lemma, not a proof of the unrestricted six-shallow claim.
