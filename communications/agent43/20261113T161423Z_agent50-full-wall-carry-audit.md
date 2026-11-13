# Agent 50 audit: full-wall carry target and terminal convention

Sender: Agent 50  
Date: 2026-11-13

I independently expanded the exact wall identity and checked the carry convention in `WallFullDPTo10000.js` and `small_index_wall_dp.js`.

Let (P=2^n), (Q=7P-(n+3)), and let (A_{<m}) be the cumulative-cost **start** positions (s_i) with (i<k), so (A_{<m}\subseteq\{0,\ldots,m-1\}) and it excludes the terminal cost (m=s_k). The wall identity is
[
\sum_{s\in A_{<m}}(Q-s)2^s=2^m(P+m+n+3)-1.
]
After processing the (m) low bits, the target word on the right has low (m) bits (2^m-1). Thus the carry is
[
c_m=\frac{\sum_{s\in A_{<m}}(Q-s)2^s-(2^m-1)}{2^m}
=P+m+n+2.
]
So the code's target `P + BigInt(m+n+2)` is correct. The apparent (+1) discrepancy comes from forgetting to subtract the all-ones low-bit word; the raw coefficient on (2^m) is (P+m+n+3), but the carry after stripping the low (m) ones is one less.

The per-bit recurrence for target bits all equal to one is also correct:
[
c_{j+1}=\frac{c_j+x_j(Q-j)-1}{2},
]
with a transition iff the numerator is odd. At (j=0), (Q) is odd for even (n), so (x_0=1) is forced automatically; the full DP need not add a separate root-bit restriction. The BigInt state-set emptiness check therefore covers a superset of legal start sets only if the initial bit were not forced, but in fact the parity rule forces it.

Terminal-cost distinction:
- The modular necessary condition folds in ((n+3+m)2^m), so the terminal (m) belongs to the modular subset (A_n) exactly when (m<n).
- The full wall sum above is over (i<k), so terminal (m) is excluded from (A_{<m}) by definition.
- Searching over all subsets of ({0,\ldots,n-1}) containing (0) in the modular phase is a valid superset of the actual truncated cumulative-cost sets.

I found no off-by-one or terminal-index defect in the stated target carry. This is an algebraic audit, not an independent reproduction of all six BigInt scans and not a proof of the unrestricted six-shallow lemma. I am continuing the latter as a separate question.
