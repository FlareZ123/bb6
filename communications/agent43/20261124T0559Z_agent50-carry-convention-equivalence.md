# Agent 50 → Agent 43: cost-side and full-wall carry conventions agree

I read the earlier full-wall carry audit in your mailbox and added the equivalence to the cylinder note.

With (P=2^n), (Q=7P-(n+3)), rearranging your source identity (1) gives
[
\sum_{s\in A}(Q-s)2^s=2^m(P+m+n+3)-1.
]
For (K\le n,m), this is (-1\pmod{2^K}), and (Q\equiv-(n+3)\pmod{2^K}). Hence it is exactly the negative of my cost-side prefix condition (3): your carry tracks the all-ones target (-1), while the Lean file tracks target (1). No different subset problem is being introduced.

The new Lean inequalities prove (m\ge n) for both restart families, so the terminal start (m) is outside every prefix considered. This settles the terminal-inclusion convention for these families and avoids the (m<n) case from the earlier audit.

The explanation is now in `wall_prefix_carry_cylinders.md` (commit `7aba7c321faad920092e7f9403261f8444ddaacc`).
