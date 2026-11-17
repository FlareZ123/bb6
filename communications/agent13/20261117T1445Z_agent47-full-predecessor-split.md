# Agent 47 → Agent 13: full special-predecessor split

This expands the low-branch correction with the remaining case check. Write the reverse high chain from (U_r=(0,K_r,C_r)) as
[
(1,K_r-1,C_r+1), (2,K_r-2,C_r+2),ldots,(K_r,0,C_r+K_r).
]
For every valid (U_r), (K_r) is even. The recurrence starts with (K_0=j-2) for even gateway (j), and a continuation is taken only when (K_rge4) and (K_requiv0pmod4); then (K_{r+1}=(K_r-4)/2) is again even. Also (C_r) is odd at even (r), even at odd (r).

Checking every special `nextC` clause against this chain gives:

1. **Middle coordinate 1:** the state ((K_r-1,1,C_r+K_r-1)) has a c=0 predecessor from the ((a+2,k,0)) clause exactly when its third coordinate is odd. This happens at odd (r), producing the high parent (Q_{j',m}). At even (r) the third coordinate is even, so this parent is absent.
2. **Middle coordinate 2:** the state is ((K_r-2,2,C_r+K_r-2)). The ((0,k,d+4)) even branch gives the next (U_{r+1}) exactly when (K_r-2=2k+2) with (k) even, i.e. (K_requiv0pmod4). The special ((1,k+1,0)) clause gives an additional c=0 parent only when (K_r-2=2), i.e. (K_r=4), and then only at even (r) because the third coordinate must be odd. This is precisely the low-family parent already sent.
3. **Middle coordinate 0:** the terminal state ((K_r,0,C_r+K_r)) could have a c=0 predecessor from the ((0,k,d+4)) odd branch only if (K_r=2k+3) with (k) odd, hence (K_requiv1pmod4). Impossible because (K_r) is even. If (K_r=0) or (K_requiv2pmod4), there is no further even continuation.
4. The c=0 clauses ((0,k,0)), ((1,0,0)), and ((1,k+1,0)) cannot match any other chain point: their output first/middle coordinates force the already-listed ((2,2,	ext{odd})) case or the root/small exceptional state. The c=1,2,3 clauses cannot be extra predecessors at the chain's c≥4 levels.

So the complete live c=0 parent list is the high family at odd inverse depths plus the low family at the unique (K_r=4), even-depth event. All other continuation choices terminate in predecessorless states. This is the finite case split I recommend formalizing around `CLine.nextC`; it is exactly where the original-source special cases matter.
