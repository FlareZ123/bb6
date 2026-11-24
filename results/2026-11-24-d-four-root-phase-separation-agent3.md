# All-time separation of the four D-family selected return orbits

Agent 3, 2026-11-24. Computer-assisted proof from the original-source uniform affine recurrence, with exact finite certificate. Strengthens the conditional phase-band argument in [Agent26's dossier](../im-results/agent26-d-phase-bands/README.md) to the total selected recurrence, including all finite suffixes. It is not a proof of nonhalting or of disjointness of arbitrary intermediate primitive configurations.

For canonical suffix s, let R(s)=length(s)+2*occurrences(011). Let (n,s) -> (n',s') be a successful return of the deterministic recurrence specified in [density-one theorem](2026-11-24-d-density-one-agent3.md). Then universally

    3 n' >= 8 n - 23,
    3 (n'+R(s')) <= 8 (n+R(s)) + 27.                 (1)

## Proof of universal inequalities

Write n=3k+d_r, d=(3,4,2), n'=8k+c. The source sweep formulas give c>=3 (for E, 11-p with p<=8; for B and A the constants are at least 9 and 5). Thus 3n'=8n-8d_r+3c>=8n-32+9=8n-23.

For E, the abstract first-exit guard certificate retains the upper gain g of the full scanned-plus-right word at each B/D sweep endpoint, before the final pop and normalization. Its exhaustive check gives max(g-p)=4, over all even classes and all possible abstract guard endpoints. If w is the actual endpoint scanned word, R(w)<=R(s)+p+4. Write l for the number of leading ones in its right tail w[1:], so R(w[1:])=l+R(s') by the rank formula (no 011 starts at a leading one). Since R(w[1:])<=R(w),

    c+R(s')=11-p+l+R(s')<=15+R(s).

For B the same argument directly gives c+R(s')=9+R(s[1:])<=9+R(s).

For A, greedily parsing a 10 token changes canonical suffix 010z to trim(0z); the rank decreases by exactly two, including the implicit-final-zero case. Parsing 111 changes 0111z to trim(0z); when z is nonempty the length decreases three and the old prefix occurrence 011 offsets any new one at the prepended zero. When z is empty the decrease is six. Hence the rank decreases by at least three. A 10 token adds two to the unary constant, a 111 token adds eight. If residual canonical word u remains after token parsing, the contribution T satisfies 3T<=8(R(s)-R(u)). The close branch has c+R(s')<=T+11+R(u). The E branch adds one pair and enters E at a suffix obtained by dropping three bits of u; this cannot increase rank, so c+R(s')<=T+2+15+R(u). In either case

    3(c+R(s')) <= 51+8R(s).

Using d_A=3 gives the second inequality of (1) with 51-24=27. The E and B bounds give smaller constants 45-32=13 and 27-16=11 respectively, since rank is nonnegative. This proves (1).

The finite guard calculation is not an empirical maximum: X is an inductive overapproximation of every finite first-left exit, and all abstract guard paths are checked, as detailed in the density-one theorem. Run [certificate.py](../im-results/agent3-d-density-drift/certificate.py); it additionally asserts max(g-p)=4, checks the anchors below, and verifies the strict interval comparisons.

## Disjoint phase bands

Define L(n)=5n-23 and U(n,s)=5(n+R(s))+27. Inequalities (1) give 3L(n')>=8L(n) and 3U(n',s')<=8U(n,s). For every successful t-return prefix from (n,s), the endpoint's five-times-unary-number lies in the real closed interval [(8/3)^t L(n), (8/3)^t U(n,s)].

Starting from the four authentic unary sections (5,9,15,39), respectively, the exact chosen evaluator reaches the following anchors:

| seed | return index (0 based) | n | suffix s | R | L | U |
|---:|---:|---:|---|---:|---:|---:|
| 5 | 10 | 123501 | 0111111 | 9 | 617482 | 617577 |
| 9 | 10 | 196699 | empty | 0 | 983472 | 983522 |
| 15 | 10 | 276715 | empty | 0 | 1383552 | 1383602 |
| 39 | 9 | 277451 | empty | 0 | 1387232 | 1387282 |

They are established by finite E/B/A replay from the genuine roots; the original blank-to-section bridges are kernel-certified. These anchor numbers agree with Agent26's earlier computation, now using the total guarded evaluator. The upper endpoint of each band is strictly below the lower endpoint of the next; moreover 3 U_39 < 8 L_5. Consequently all bands for every nonnegative t, ordered by (t, anchor order), are pairwise disjoint. This holds for every defined successful return, whether the trajectory eventually halts or not. No two selected macro endpoints at or beyond their anchors can have the same unary length, even with different indices or exceptional suffixes.

There is no overlap with earlier endpoints: all pre-anchor unary lengths are smaller than the minimum anchor (max pre-anchor 104043 < 123501). The finite pre-anchor lists have no equal full (n,s) pair (the two n=289 cases have different suffixes). This last finite check follows by the same evaluator. Hence the four *selected* macro orbits never intersect as full canonical section configurations. This statement deliberately does not claim that the raw primitive orbits cannot intersect between selected returns, because the chosen total source recurrence is not required to be the least positive return.

This removes the conditional regular-branch assumption in the earlier phase-band argument. It gives a useful structural constraint on any proposed shared inductive invariant for the four roots, but no individual halt decision. Verification status: source recurrence and genuine entry bridges previously kernel-certified; the new guard bound and anchor calculation are exact Python certificate checks, with the remaining inequalities proved above. No new unconditional BB(6) bound follows.
