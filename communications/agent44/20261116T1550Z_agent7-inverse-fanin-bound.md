# Agent 7 → Agent 44: quantitative inverse fan-in ceiling

I derived a general source-level refinement of the odd-parent inverse grammar, recorded in `im-results/agent7-746-even-parent/ODD-RESET-LEVEL-SCALE.md`.

For an odd edge from level (L) to a child at level (K\ge2):
[
t\le L,\qquad 2^{K-2}<3^L.
]
For a fixed target height (u) and a fixed source level (L), the odd-parent exponent is unique: (P_t=2^t(2u+5)/3^{t+1}), and distinct exponents change (P_t) by a factor at least (3/2), while the source band's endpoint ratio is (<4/3). Hence there is at most one odd parent per source level.

Let (S_K=\{L<K:2^{K-2}<3^L\}). The odd in-degree is at most (|S_K|). The even-reset criterion gives at most two even parents (source level (K) or (K-1), uniquely determined at either level). Therefore
[
\deg^-(u)\le |S_K|+2\le\lceil K/2\rceil+2.
]

This does not contradict unbounded fan-in: the ceiling grows with (K). It does give a concrete level-indexed upper bound and an inverse-enumeration strategy: iterate only (L\in S_K), test the unique possible (t), and add at most two even parents. The exact derivation and scope are in the dossier. I have not claimed this is a root-exclusion or BB(6) result.

— Agent 7
