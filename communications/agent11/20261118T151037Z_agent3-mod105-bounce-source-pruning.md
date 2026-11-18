# Agent 3 → Agent 11: mod-105 root restriction and mod-3 pruning of every B_r source fan

I derived an additional exact restriction from the authentic U5 residual identity, recorded in `im-results/agent3-c-bounce-inverse/U5Q0ResidualMod105.md`.

Assuming
`211*t+1360+22155*w = 20*2^(201+3360*w)`
and `t=39+64*h`, reductions mod 3, 5, and 7 give
`h ≡ 84 (mod 105)`, hence `S=416+684*h ≡17 (mod 105)`.

For every remaining fan depth `r>=1`, `4^r*q=S`; therefore q mod105 is one of
`17,83,47,38,62,68` according to r mod6, so q>=17 and the first coordinate of B_r is at least 32.

More importantly, the mod-3 part prunes the *source grammar* for every B_r:
- h≡0 mod3, S≡2 mod3, 4^r≡1 mod3, so q≡2 mod3;
- for B_r=(x,y)=(2q-2,2487+4096h-q-3r), x+y≡0 mod3;
- the exceptional a=0 source branch requires x+y=8*2^n and cost parity forces n odd, making the right side 1 mod3, impossible;
- the exceptional a=1 source branch requires x+y+1=16*2^n and again n odd, making the right side 2 mod3 while the left is 1 mod3.

Thus every B_r incoming edge must be direct or one of the nonexceptional bounce branches. This is a uniform reduction across all r, not a reachability exclusion. The note is paper-level arithmetic, not yet Lean-compiled.

Please check the branch equations against your exact `section_preimage_all_iff` and consider integrating this pruning before continuing the Q+r mod4 residual split. In particular, it may simplify a generic all-depth parent theorem for B_r.
