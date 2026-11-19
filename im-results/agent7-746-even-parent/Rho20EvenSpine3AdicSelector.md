# 3-adic selector for odd branches on the rho-20 even spine

**Status:** structural lemma and representative lifts; not a complete root-exclusion proof for the `a mod 54 = 2,20` phases. This belongs in `im-results/`.

## Spine numerator

For the rho-20 residual family with
[
K=97\cdot2^{a-7}+48,\quad p=2^K,\quad q=2^{K-a},\quad L=K-2,
]
the two initial (t=0) odd inversions lead to
[
D_0=(26368q+47K+31)/27,\quad
G=D_0+L=(26368q+74K-23)/27.
]
The same-level even spine is
[
D_j=2^jG-L,\qquad y_j=2p-D_j.
]
Its odd-parent numerator is exactly
[
X_j=2y_j+5=A-2^{j+1}G,
\qquad A=4p+2K+1.
]

For the two unresolved modulo-54 phases:
- (a\equiv20\pmod{54}): (A\equiv6\pmod9), (G\equiv3\pmod9);
- (a\equiv2\pmod{54}): (A\equiv6\pmod9), (G\equiv6\pmod9).

Thus (A=3A'), (G=3G'), with (A',G') both units modulo 3, and
[
X_j=3(A'-2^{j+1}G').
]

## Unique Hensel selector

For every (m\ge1),
[
3^{m+1}\mid X_j
\iff
2^{j+1}\equiv A'(G')^{-1}\pmod{3^m}.
]
The order of (2) modulo (3^m) is exactly (2\cdot3^{m-1}): by LTE,
[
v_3(2^{2\cdot3^r}-1)
=v_3(4^{3^r}-1)=r+1.
]
Hence (2) generates ((\mathbb Z/3^m\mathbb Z)^\times), and for every threshold (m+1), the indices (j) with (v_3(X_j)\ge m+1) form exactly one residue class modulo (2\cdot3^{m-1}).

This is an exact selector for the high-valuation positions on the spine, rather than a finite scan. It is the natural place to translate Agent 7's earlier Hensel-selector machinery.

## First lifts at representative parameters

| Parameter | (A\bmod27) | (G\bmod27) | (A'/G'\bmod27) | (v_3(X_j)\ge2) | (\ge3) | (\ge4) |
|---|---:|---:|---:|---|---|---|
| (a=20) | 15 | 21 | 20 | (j\equiv0\pmod2) | (j\equiv0\pmod6) | (j\equiv6\pmod{18}) |
| (a=56) | 15 | 15 | 1 | (j\equiv1\pmod2) | (j\equiv5\pmod6) | (j\equiv17\pmod{18}) |

For higher lifts the target (A'(G')^{-1}) must be computed modulo higher powers of 3; it depends on the parameter's further 3-adic phase.

## Dyadic admissibility of an odd exponent

On the long spine, (y_j/p\) is close to (2), so the limiting source coordinate for odd exponent (t) is
[
\frac{P_t}{p}\longrightarrow
\frac{2^{t+2}}{3^{t+1}}.
]
A limiting odd-parent band exists precisely when this ratio lies in
[
[6\cdot2^c,\,8\cdot2^c]
]
for some integer (c). The first admissible exponents are
[
1,3,6,8,11,13,15,18,20,23,25,27,30,32,35,37,39,\ldots
]
This is a rotation coding under the irrational angle (log_2(3/2)), not a periodic sequence. The limiting test is only a branch-discovery aid: exact finite-parameter inequalities, including the (+1/-1) source-band endpoints, are still required in any proof.

## What remains

The Hensel selector determines *where* the spine can have large 3-adic valuation. To finish either open phase one must combine:
1. the unique residue class of (j) for each valuation threshold;
2. the admissible (t)-set from the dyadic source bands;
3. exact finite-(a) error bounds for the source coordinate;
4. the inverse-parent analysis of each resulting off-spine branch.

No claim is made here that those off-spine branches all terminate.
