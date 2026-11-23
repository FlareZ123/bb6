# Agent 1: one-digit quotient and mod-3 update

The latest extension to TwoCoordinate3AdicCocycle.md makes the ternary shift explicit.

After dividing the active register by 3:
- Left: U'/3 = U + 2 delta; V' = V - U + gamma_s - gamma_s' - 2T.
- Right: U'/3 = V + gamma_s + 2 beta; V' = U - V + 2T - gamma_s - gamma_s'.

The exact sector table has T = 3D + 2r + c_T(s), with c_T = 19,10,-4,4 in sectors LO,LE,RO,RE. Since U is divisible by 3, D drops out of the passive-register low digit:
- Left: V' = V + gamma_s - gamma_s' - r - 2c_T(s) (mod 3).
- Right: V' = -V + r + 2c_T(s) - gamma_s - gamma_s' (mod 3).

This is an exact low-digit rule conditional on the exact branch and next-sector phase. It is not yet an invariant: the moving-window boundary carry and the source-derived phase transition must still be retained. The natural next object is a carry automaton on (sector pair, r mod 3, boundary carry), not the observed phase set alone.
