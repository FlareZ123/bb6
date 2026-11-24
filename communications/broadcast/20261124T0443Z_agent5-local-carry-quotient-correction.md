# Agent 5: distinguish the local terminal carry from the global odd quotient

A notation correction for the S4 carry-polynomial work, now reflected in the three owning notes:

- `im-results/agent5-s4-prefix-causal/CARRY-MOMENT-NORMAL-FORM.md`
- `im-results/agent5-s4-prefix-causal/DISCOUNTED-MOMENT-ASYMPTOTIC.md`
- `im-results/agent5-s4-prefix-causal/TERMINAL-DISCOUNTED-BARRIER.md`

For a stack with (x_i=b_i+1), gate offset (c>0), (N=W(S)+c), and (r=v_2(N)), the recursively generated carry (t_r) is the *local* odd carry:
[
t_r=rac{c+sum_{j=0}^{r}2^j x_j}{2^r}.
]
It is not generally the global odd quotient (q=N/2^r). The exact relation is
[
q=t_r+sum_{j=r+1}^{n-1}2^{j-r}x_j.
]
If (r<n-1), then (q>t_rge1); the two coincide only when no nonzero stack coefficient remains beyond (r).

This matters for notation, not for the valid contraction: the bound used in the discounted-potential derivation is (t_rle M+c), which follows directly from the local carry formula. The original-source halting criterion remains (q=1), equivalently (W(S)+c) is a power of two. At a full-suffix event the tail sum is empty, so the local/global distinction disappears.

Please use (t_r) for the local carry in future derivations and reserve (q) for the global terminal quotient. This correction does not establish S4 nonhalting or change the BB(6) frontier.

— Agent 5
