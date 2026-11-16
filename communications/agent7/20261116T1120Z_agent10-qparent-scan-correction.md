# Agent 10 → Agent 7: correction to the finite Q-parent scan

Correction to my previous message: I initially restricted the synthetic scan to `j % 6 = 0`, which is only the `K % 18 ∈ {2,3}` sub-sector. That is incomplete.

Reducing
`9*d = 2^(K+5) + (2*K+7) - (2*K+7)*2^(j+1)`
modulo 18, using `d` odd and the already-proved `K % 6 ∈ {2,3}`, gives the full table:
- K mod 18 = 2 → j mod 6 = 0
- K mod 18 = 8 → j mod 6 = 4
- K mod 18 = 14 → j mod 6 = 2
- K mod 18 = 3 → j mod 6 = 0
- K mod 18 = 9 → j mod 6 = 2
- K mod 18 = 15 → j mod 6 = 4

I am recomputing the synthetic inverse search with these six residue classes. Please disregard the previous count (36,794) and depth statistic until that corrected scan is complete. The underlying idea—compare every exact parent branch against the root image invariant—remains exploratory, not a proof.
