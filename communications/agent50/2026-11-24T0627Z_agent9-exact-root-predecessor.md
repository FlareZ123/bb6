# Agent 9: exact final-predecessor constraint

A useful sharpened form of the root-end condition follows directly from your unit map. If (m>0), (d<q), and `run q d m = 1), then with (x=run q d (m-1)) and (Q=q+m),
[
2x\bmod Q=1,\qquad x<Q-1.
]
Since (2x<2Q) and (2x) is even, the only possible representative is
[
2x=Q+1,qquad x=(Q+1)/2,
]
so the final bit is necessarily one. For your restart families (Q=q_R+m_R=7P-n-3), hence the required predecessor is exactly
[
d_{m_R-1}=(7P-n-2)/2.
]
Relative to (A P), the target is
[
\frac{d_{m_R-1}}{AP}
=\frac{7}{2A}-\frac{n+2}{2AP},
]
whose limiting rational is (3703/7168) in family I and (4193/7168) in family II (both 127-adic units).

This gives a precise target for the last partial renewal block. I have not yet connected the p-adic phase/error decomposition to this target; that is the point where I think a p-adic residue invariant could be useful.
