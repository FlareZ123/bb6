# Agent 7: 3-adic Hensel selector on the rho-20 even spine

A further structural reduction for the two still-open class-2 phases (`a mod 54 = 2,20`):

Along the same-level even spine write
`X_j = 2 y_j + 5 = A - 2^(j+1) G`,
where `A=4p+2K+1` and `G=D0+(K-2)`.

For these two phases, the mod-9 residues are:
- `a mod 54 = 20`: `A = 6 (mod 9)`, `G = 3 (mod 9)`;
- `a mod 54 = 2`: `A = 6 (mod 9)`, `G = 6 (mod 9)`.

Thus `A=3A'`, `G=3G'` with both A' and G' units modulo 3, and
`X_j = 3(A' - 2^(j+1) G')`.

For every m≥1:
`3^(m+1) | X_j` iff
`2^(j+1) = A' * (G')^(-1) (mod 3^m)`.

Since 2 has exact order `2*3^(m-1)` modulo `3^m` (LTE applied to `4=1+3`), it generates the unit group. Consequently, for every valuation threshold m+1, the indices j with `v3(X_j) ≥ m+1` form **one residue class modulo `2*3^(m-1)`**, not an arbitrary set. This gives a unique 3-adic/Hensel selector for all higher odd-parent branches along the even spine.

The first lift is already explicit:
- mod-54 phase 20: `A'/G' = 2 (mod 3)`, so `j` is even for `v3(X_j)≥2`;
- mod-54 phase 2: `A'/G' = 1 (mod 3)`, so `j` is odd.

The limiting odd-parent source coordinate for exponent t on this spine is
`P_t/p → 2^(t+2)/3^(t+1)`.
Its dyadic-band admissibility is the rotation condition that this ratio lie in `[6*2^c, 8*2^c]` for some integer c. The first admissible t values are
`1, 3, 6, 8, 11, 13, 15, 18, 20, 23, 25, 27, 30, ...`.
This is a log-rotation/Sturmian-type selector (slope `log2(3/2)`), not a periodic list. Exact finite-a corrections still need uniform bounds before using this limiting list as a proof.

The mod-54=38 phase is now separately excluded in `im-results/agent7-746-even-parent/Rho20Class2-38mod162.md` (updated theorem covers all mod54=38). This Hensel selector is aimed at the remaining mod54=2,20 branches.
