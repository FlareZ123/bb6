# Dual 3-adic Hensel tower in inverse-ray depth for unresolved #746

**Agent 7, 2026-11-05.** Exact mathematical theorem with a complete elementary paper proof and independent modular tests. **Not yet Lean-formalized as a joint theorem.** The depth-zero fatal-index tower is already original-source Lean certified in [FatalHenselResidue.lean](FatalHenselResidue.lean), while the odd-level source-root forced-parent theorem is certified in [OddRayForced.lean](OddRayForced.lean). This note adds a genuine new mathematical structure, but no blank-root reachability decision.

## Signed symbolic numerator

Fix any fatal index (n\ge4) with (n\bmod6\in\{4,5\}). Define the canonical even-ray deficit and signed inverse input by
[
D_j(n)=2^j(2n+3)-(n-1),qquad
Z_j(n)=8\cdot2^n-2D_j(n)+5.
]
The closed formula for (D_j) is proved in unchanged source Lean by [OddRayDeep.lean](OddRayDeep.lean), original-source [CI 42122191076](https://github.com/FlareZ123/bb6/actions/runs/42122191076). In particular, write
[
A_n=8\cdot2^n+2n+3,qquad B_n=2n+3.
]
Then the identity over **signed integers** is
[
\boxed{Z_j(n)=A_n-B_n\,2^{j+1}.}\tag{1}
]
Because (n\bmod6\in\{4,5\}), (3\nmid B_n) and (A_n/B_n\equiv2\pmod3), where division means multiplication by the inverse modulo three. The signed expression is essential: actual source reset heights (U_j(n)=4\cdot2^n-D_j(n)) eventually become negative at large (j). Only the part of the ray with (U_j(n)\ge0) corresponds to candidate physical reset heights.

## Exact depth-residue theorem for every 3-adic precision

**Theorem (proved on paper).** For each natural (k\ge1), set (L_k=2\cdot3^{k-1}). There is a unique residue
[
0\le r_{n,k}<L_k
]
such that, **for every (j\ge0)**,
[
\boxed{3^k\mid Z_j(n)\quad\Longleftrightarrow\quad
j\equiv r_{n,k}\pmod{L_k}.}\tag{2}
]
The residue is even, and residues lift uniquely: (r_{n,k+1}=r_{n,k}+t_k L_k), for a unique digit (t_k\in\{0,1,2\}). In particular (r_{n,1}=0).

### Elementary proof

For (k=1), (3\mid Z_j(n)) iff (2^{j+1}\equiv2\pmod3), which holds exactly for even (j), proving (r_{n,1}=0), (L_1=2).

We need the exact elementary power-lift fact:
[
\boxed{2^{L_k}=1+3^k c_k,\qquad3\nmid c_k.}\tag{3}
]
At (k=1), (2^2=4=1+3\cdot1). If (x=2^{L_k}=1+3^k c_k), then (2^{L_{k+1}}=x^3), and
[
\frac{x^3-1}{3^{k+1}}
=c_k+3^k c_k^2+3^{2k-1}c_k^3
\equiv c_k\not\equiv0\pmod3,
]
because (k\ge1). This proves (3) by induction, with (L_{k+1}=3L_k). No appeal to external primitive-root theorems is required.

Suppose the unique residue (r_{n,k}) is known. Since (3) makes (Z_j(n)\pmod{3^k}) periodic with period (L_k), any solution modulo (3^{k+1}) must reduce to one of the three indices (j=r_{n,k}+tL_k) with (t=0,1,2). Using (1) and (3),
[
Z_{r+tL_k}(n)
\equiv Z_r(n)-B_n2^{r+1}\,t3^k c_k
\pmod{3^{k+1}}.
]
The three possible quotients modulo 3 differ by the nonzero unit (B_n2^{r+1}c_k\pmod3), so **exactly one** choice of (t) is divisible by (3^{k+1}). This supplies the next unique lift. Periodicity at precision (k+1) follows from (3) at the next level. Complete induction proves (2).

Unlike a finite search or a sampling assertion, (2) is a fully quantified statement covering **all** symbolic ray depths and every 3-adic precision.

## Exact depth-density law, independent of the fatal-index Hensel theorem

A periodic residue class of modulus (L_k) has natural density (1/L_k). Thus, **for every fixed qualifying (n)**, the signed continuation has

[
\operatorname{dens}\{j\ge0:v_3(Z_j(n))\ge k\}
=\frac1{2\cdot3^{k-1}},\quad k\ge1.
\tag{4}
]

The exact limiting valuation distribution over all formal ray depths is
[
\boxed{
\operatorname{dens}\{v_3(Z_j(n))=0\}=\frac12,
\qquad
\operatorname{dens}\{v_3(Z_j(n))=k\}=\frac1{3^k},\quad k\ge1.
}
\tag{5}
]
For the **even** subsequence (j=2h), the tail density of valuation at least (k) is (3^{1-k}), exactly mirroring the already-source-verified density over fatal *indices* at any fixed even ray depth.

This duality is the central mathematical point: the congruence surface
[
8\cdot2^n+2n+3-(2n+3)2^{j+1}\equiv0\pmod{3^k}
]
has a unique Hensel lift in the fatal-index direction for fixed even depth (paper generalization of the kernel-proved depth-zero tower), and a unique Hensel lift in the inverse-depth direction for every fixed surviving fatal index. Their periods are different: the fatal-sector index has period (3^{k-1}), while the full ray depth has period (2\cdot3^{k-1}). These are exact modular **facts** rather than a probability model for the Turing machine's deterministic orbit.

### Connection to the six-step sparse-fork pattern

At (k=2), the exact period is (L_2=6), with one 9-divisible ray depth per six positions. At all other five positions an eligible high-ray source reset target has a uniquely forced even predecessor, by the source's complete inverse grammar and the exclusion of odd (t=0) near the upper dyadic band; see [RayForkPeriodicity.md](RayForkPeriodicity.md). For (k=3), the single potentially more branching position among those six occurs once per 18 symbolic ray positions; likewise at all higher 3-adic precisions. Inverse branch complexity therefore has a nested deterministic ternary sparsity pattern along this ray.

**Important domain:** The density statements (4) and (5) are computed over all (j\ge0) in the signed *formal* continuation. For a **fixed** finite fatal index (n), only finitely many ray heights (U_j(n)) are nonnegative. Hence these densities are **not** automatically densities of physically admissible source reset nodes, nor actual blank-derived ancestors. Applying the pattern to a long true-source admissible prefix requires increasing (n) in tandem with the depth cutoff.

## Independent finite modular diagnostics

Exhaustively checked the first complete period modulo (3^k), for all (k\le6), with ordinary integer arithmetic using modular exponentiation. Representative unique depth residues:

| Fixed (n) | (r_{n,1}\bmod2) | (r_{n,2}\bmod6) | (r_{n,3}\bmod18) | (r_{n,4}\bmod54) | (r_{n,5}\bmod162) | (r_{n,6}\bmod486) |
|---:|---:|---:|---:|---:|---:|---:|
| 100 | 0 | 4 | 10 | 28 | 28 | 28 |
| 101 | 0 | 2 | 8 | 26 | 134 | 458 |
| 202 | 0 | 0 | 12 | 48 | 102 | 264 |
| 203 | 0 | 0 | 12 | 48 | 156 | 156 |

These calculations corroborate the symbolic lift, not a substitute for its induction proof.

## Research implications and next experiment

The exact ray-depth tower gives a constructive, fast arithmetic method to predict the unique precision-(k) branching level among a large interval of **formal ray positions**. Combined with the already source-verified forced-parent iff, this enables an aggressive compressed inverse-graph search that skips five of every six ray positions and focuses on sparsely located genuine fork candidates.

To help solve #746, a further **root-specific** argument is essential: show an invariant separating the true source root (C(2,0)) from all surviving infinite fatal gates, or produce an authentic halting witness. Neither (2) nor the root-preserving forced-step transport resolves either task, and they do not establish a value of BB(6).

**Next reproducible proof task:** formalize the modular lift (3) and uniqueness (2) in Lean using `OddRayDeep.lean`, then prove the source reset-parent corollary via `FirstInverseComplete.lean` and `FourEven.lean`. Preserve the signed-to-nonnegative ray domain bridge explicitly.
