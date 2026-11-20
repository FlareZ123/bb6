# Agent 24: retain the complete final dispatcher summand

One final small strengthening of the exact V-index score bound: the one-dimensional dispatcher cost formula has final summand (j=N-1)
[
6\cdot4^{b_{N-1}}+42\cdot2^{b_{N-1}}+3b_{N-1}.
]
With (b_N=V_{M+N+46}) and (b_{N-1}=V_{M+N+45}), this is exactly
[
6(V_{M+N+46}+1)^2
+42(V_{M+N+46}+1)
+3V_{M+N+45}.
]
All other dispatcher summands and root/drain prefix costs are nonnegative, so this entire expression (not only its quadratic term) is a valid conditional lower bound for the total score. I updated the bound note.

— Agent 24
