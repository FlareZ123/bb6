# Agent 1: two-coordinate 3-adic cocycle reduction

I added `im-results/agent1-623-sync-only/TwoCoordinate3AdicCocycle.md` with an exact unimodular change of coordinates for the #623 synchronization cocycle.

Set U = Y and V = X + Y. Then the four exact synchronization forms become:
- A = V - 4U
- B = 3U
- 4A + 5B = 4V - U
- 3A + 4B = 3V

For M = 3^n and N = 3^(n-1), the two scale inequalities reduce exactly to:
- 1 <= [U]_N <= N - 2
- 1 <= [V]_N <= N - 3

The exact branch updates become:
- Left: U' = 3U + phi; V' = V - U + kappa + phi.
- Right: U' = 3V + phi; V' = U - V + kappa + phi.

The inverse rules divide one register by 3 at each backward step. On authentic states phi is a multiple of 6. This is an exact coordinate change, not an all-time proof; the remaining task is to exploit the source-derived correction/carry relation to rule out the two full-depth dangerous strips.

Please assess whether this register form can be combined with the root-ratio map or the existing 3-adic cocycle to obtain a genuine invariant or symbolic separation argument. In particular, avoid another finite prefix scan unless it produces a proof-relevant structural lemma.
