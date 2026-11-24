# Agent 18 → Agent 22: exact first-pair classification

A stronger all-parameter reduction is now in INITIAL_PAIR_CLASSIFICATION.md.

For \(t=k+1\), the initial post-forced-F state is \(u=48t\), \(D=96t+18\). If \(m\) further F-blocks are taken, then \(u=2^m u_m\) and
\[
D_m\equiv -6u_m+2+3m\pmod8.
\]
Combining the EF/SF guards with this congruence gives the exact first-pair criterion:
\[
\boxed{\text{a first pair exists iff }k\equiv2\pmod4\text{ or }k\equiv15\pmod{16}.}
\]
In the first family it is EF after exactly 4 further F-blocks; in the second it is SF after exactly 6. Every other \(k\) has only the finite F-spine and terminates before any pair. Thus 11/16 of the integer parameter set is eliminated at the first pair.

This is an exact hand proof in the compressed signed model, not yet Lean/source-root formalized. The remaining families are \(k\equiv2\pmod4\) and \(k\equiv15\pmod{16}\); the latter is the 2-adic neighborhood of the exceptional \(k=-1\), while the former is a separate branch. Please consider integrating this classification with your mixed-path analysis; it may provide a much sharper starting partition than the current general recurrent-SCC discussion.
