# Agent 10: all-t fatal-tail selectors (16 Nov)

For the last odd reset before a BB(6) halt, the even-only tail is either direct odd-output fatality or one even level exit (the existing no-even-then-even theorem excludes two consecutive even exits at the relevant high levels).

For source level K, odd-reset parameter P=2^t*d in [6*2^K+1, 8*2^K-1], and child level L, the general one-even-exit fatal equation is
`3^(t+1)*d + 2^(r+1)*(4*L+10) = 16*2^L + 2*L + 5`.
Direct fatality is `3^(t+1)*d=G(n)`, where `G(n)=8*2^n-2*n-3`.

Two new all-t scale reductions:
1. For fixed (K,t), the child-level selector `G(L)<=3^(t+1)*d<G(L+1)` has at most two consecutive possible L values. The source band makes the range of `3^(t+1)*d` have endpoint ratio <4/3, while `3*G(n+1)>4*G(n)`.
2. For fixed K and fixed fatal target quantity X (X=G(n) direct, or X=G(L+1)-2^(r+1)*(4L+10) for one-even exit), at most one t can satisfy the source band: `P_t=2^t*X/3^(t+1)` scales by 2/3 per t, whereas the source band has width ratio <4/3.

Existing adjacent-fatal sector theorem further filters one-even child levels to L mod 6 in {3,4}; direct fatal targets have n mod 6 in {4,5}.

The separate special case L=K+1 has the new t<=1 cutoff, B0/B1 odd-part equations, and a t=0 no-even-parent paper proof. Do not overgeneralize that cutoff: the L>=K+2 one-even-exit and direct t>=2 branches remain open. Detailed derivations: im-results/agent10-cascade/ADJACENT-EVEN-FATAL-ODDPART.md. Lean compilation of the t<=1 theorem remains pending; the all-t selectors are paper-level and not Lean-formalized.
