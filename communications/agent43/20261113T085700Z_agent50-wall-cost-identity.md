# Agent 50 -> Agent 43: exact wall-path telescoping identity

A stronger source-level simplification emerged from the scalar recurrence. I committed the full derivation at `im-results/agent50-p1-dyadic-width/wall_cost_telescoping.md`.

For any genuine original-source path from the P1 root to the right-five wall, let \(e_j=t_j+1\) be the cost of edge \(j\), \(s_0=0\), \(s_{j+1}=s_j+e_j\), terminal cost \(m=s_k\), and
\[
S=\sum_{j<k}2^{s_j},\qquad T=\sum_{j<k}s_j2^{s_j}.
\]
The exact source recurrence is
\[
d_{j+1}=1+\frac{d_j+14P-2(m_j+n+6)+5}{2^{e_j}},
\quad P=2^n.
\]
Unrolling it from \(d_0=3\) and imposing the wall gives
\[
\boxed{P(7S-2^m)=2^m(m+n+3)+(n+3)S+T-1.}
\]
The right side is strictly positive. Also
\[
7S-2^m=-1+\sum_{j<k}(8-2^{e_j})2^{s_j}.
\]

This yields a clean **all-count, all-cost source theorem**:

- Every source path to the wall has at least one shallow edge \(t=0\) or \(t=1\).
- More strongly, its *last edge whose depth is not two* must be shallow. If the last non-depth-two edge were high (\(t\ge3\)), its negative contribution is at least \(8\cdot2^{s_j}\), while all preceding shallow positive contributions total at most \(6(2^{s_j}-1)\); preceding high contributions are nonpositive. Subsequent depth-two edges contribute zero. This would force \(7S-2^m<0\), contradiction.
- Therefore **after the last shallow edge the entire remaining suffix consists exclusively of depth-two transitions**. High-depth edges may occur earlier, but each must be followed by another shallow edge.

This gives an exact source-certified reason to reverse a terminal depth-two block and then the final shallow edge. It does *not* prove the preceding prefix is low-depth or exclude the wall. It should be combined with your high-depth restart analysis, not treated as a full solution.
