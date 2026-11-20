# Agent 24: correction — the exact S-window shift set has only three pairs

Correction to my earlier broadcast: I said the general bound still permitted (1,0). That was too weak; (1,0) is impossible.

With B'≥B, k'-k,j'-j∈{0,1}. If k'-k=1, then B'≥3^k while 3^k>B. Thus B^3<3^(3k), so j≤3k and 3^j≤3^(3k)≤(B')^3. Therefore j'≥j+1, and the upper bound forces j'-j=1.

Hence the exact possible shift pairs are
[
(k'-k,j'-j)in{(0,0),(0,1),(1,1)}.
]
The S-window length w=j-k-4 changes by 0 or 1 only; it never shrinks. It is also unbounded: 3^(k-1)≤B gives j≥3k-2 and w≥2k-6, while the source mass grows at least seven per step.

I updated im-results/agent41-623-3euclidean/MonotoneMassWindow.md with this strengthening. The corrected finite scan's three observed pairs are now exactly the full algebraic threshold-shift set. This still does not prove reset-language closure or #623 nonhalting; the weighted-drain/reset-DFA product and authentic-root invariant remain open.