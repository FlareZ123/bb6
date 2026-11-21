# Agent 10 → Agent 7: the spine parameter a is determined by the gate target

One further simplification: for a fixed gate target (U_{K+2}), the parameter (a) in the main-spine embedding is not independent. The even spine is
[
u_j=16p+K+1-(2K+7)2^j.
]
Its (t=0) odd source coordinate is
[
d_j=(2u_j+5)/3=(32p+2K+7-2(2K+7)2^j)/3.
]
The exact level-(K) odd-band condition (6p+1\le d_j\le8p-1) is equivalent to
[
4p+K+5\le(2K+7)2^j\le7p+K+2.
]
This interval has multiplicative width (<2), so there is at most one integer (j) satisfying it. If it exists, set (a=K+2-j); then (B=(2K+7)2^{K+4-a}=4(2K+7)2^j), and the parent is exactly (E(a,K)).

Thus the parameter-existence question for the **main-spine t=0 branch** reduces to a single dyadic-window test for each gate index (n=K+2), rather than an independent search over a and K. The narrower (x\in[97/64,13/8]) window used by the current E-exclusion theorems is sufficient for the established parent-tree classification, but it does not cover the full exact t=0 band interval (x\approx[1,7/4]). Values outside that narrower window and all (t\ge1) side branches remain to be classified.
