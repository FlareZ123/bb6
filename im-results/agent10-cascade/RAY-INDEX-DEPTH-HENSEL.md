# Dual 3-adic Hensel coordinates on the #746 fatal inverse ray

**Status (12 November 2026):** the arithmetic derivation is complete; `RayIndexHensel.lean` is a Lean proof draft added to the existing manual source-check workflow, but that workflow has not yet been run on this revision. This is an intermediate result, not a blank-root exclusion and not a BB(6) solution.

## Statement

Write the signed canonical-ray numerator as
[
Z_j(n)=operatorname{signedZ}(n,j)
=8cdot2^n-2(2^{j+1}-1)n+3(1-2^{j+1}).
]
For either surviving fatal sector (sin{4,5}) and every **even** depth (j), there is a unique residue
[
R_{s,j,k}in{0,ldots,3^k-1}
]
such that, for every (hge0),
[
3^{k+1}mid Z_j(s+6h)
quadLongleftrightarrowquad
hequiv R_{s,j,k}pmod{3^k}.
]
The residue is constructed recursively. With (R_{s,j,0}=0), set
[
q_k=rac{Z_j(s+6R_{s,j,k})}{3^{k+1}},
qquad
R_{s,j,k+1}=R_{s,j,k}+3^k(q_kmod3).
]
The Lean definition uses the existing `henselDigit` and coefficient (4(2^{j+1}-1)); this coefficient is (1mod3) when (j) is even, so its digit is exactly (q_kmod3).

## Exact shift calculation

Let (P=3^{k+1}) and (D=2cdot3^{k+1}=6cdot3^k). The existing depth-period identity gives
[
2^D=1+3^{k+2}c_{k+1}.
]
Consequently, with (a_j=2^{j+1}-1),
[
Z_j(n+D)=Z_j(n)-4a_jP+3P,(8cdot2^n c_{k+1}).
]
More generally, for the three lift digits (t=0,1,2),
[
Z_j(n+tD)equiv Z_j(n)-4a_jPtpmod{3P}.
]
Because (a_jequiv1pmod3) for even (j), exactly one of the three choices of (t) lifts divisibility from (P) to (3P).

The stride (D=6cdot3^k) is precisely the change in (n=s+6h) when (h) is increased by (3^k). Thus the divisibility predicate is periodic in (h) modulo (3^k) at precision (3^{k+1}). At precision one, the existing theorem `signedZ_mod_three_even_iff` supplies the base case for (s=4,5) and even (j). Induction gives the unique residue class at every precision.

## Duality with the existing depth selector

The existing `RayDepthResidue.lean` theorem fixes (n) and selects the unique depth residue modulo (2cdot3^k). The new `indexResidue_iff` theorem fixes even (j) and selects the unique sector-index residue modulo (3^k). They describe the same divisibility relation, so
[
jmod(2cdot3^k)=operatorname{depthResidue}(s+6h,k)
quadLongleftrightarrowquad
hmod3^k=R_{s,j,k}.
]
The Lean theorem `depth_index_duality` states this equivalence. The stronger `indexResidue_bijective` statement says that, in each sector and at each precision, the even depth classes in one depth period are in bijection with the sector-index classes. Thus the two Hensel selectors are inverse coordinates of one 3-adic congruence surface, not two unrelated residue tests.

For the first packet ((k=1)), the bijection is explicit:
- Sector (s=4): (j=0,2,4) correspond respectively to (h=0,2,1pmod3).
- Sector (s=5): (j=0,2,4) correspond respectively to (h=0,1,2pmod3).

## Nested odd-parent numerator at arbitrary even depth

The same mechanism applies after an odd parent of **any** even-depth canonical ray node. If
[
x=2^t d,qquad 3^{t+1}d=Z_j(n),
]
then
[
2x+5=rac{W_{j,t}(n)}{3^{t+1}},qquad
W_{j,t}(n):=2^{t+1}Z_j(n)+5cdot3^{t+1}.
]
For (s\in\{4,5\}) and even (j), (W_{j,t}(s+6h)\equiv0\pmod3) for every (h,t). Its exact three-digit shift is
[
W_{j,t}(n+rD)
\equiv W_{j,t}(n)-3^{k+1}2^{t+3}(2^{j+1}-1)r
\pmod{3^{k+2}},
\qquad D=2\cdot3^{k+1},\quad r\in\{0,1,2\}.
]
The coefficient (2^{t+3}(2^{j+1}-1)) is a 3-adic unit for even (j). The Lean draft therefore proves `nestedOddNumerator_sector_mod_three`, the exact criterion `nestedOddNumerator_lift_criterion), and `nestedOddNumerator_unique_lift): whenever (3^{k+1}\mid W_{j,t}(n)), exactly one of the three next index digits preserves divisibility at (3^{k+2}).

This is a complementary index-coordinate form of the translated high-gate Hensel selectors already used for (t=3): those fix the fatal index and solve for a depth class, while this theorem fixes the even depth and solves for the fatal-index digit. It can be iterated to build the full (W_{j,t}) residue selector; the recursive selector itself has not yet been added. The unique-digit theorem is already reusable for exceptional high-valuation feeder branches.

## BB(6) relevance and strict boundary

An odd inverse parent at ray node (Z_j(n)) requires the appropriate divisibility (3^{t+1}mid Z_j(n)), in addition to the dyadic source-band condition. The selector therefore locates, exactly and at every valuation threshold, the fatal-sector indices at which a fixed even-depth node can have the required 3-adic valuation. The duality also identifies the unique even-depth class for a fixed fatal index.

This does **not** establish the dyadic band, does not show that any such odd parent is reachable from the blank root, and does not exclude the even fatal predecessor. It is a parameterization of potential odd exits along the canonical even ray, intended to support the still-open root-sensitive even-parent analysis. Keep it in `im-results/` until Lean source CI and adversarial review succeed; do not promote it to `results/` merely because the arithmetic theorem is clean.
