# Aperiodic shadow paths cannot consist of uniformly long direct blocks

**Scope.** A new deterministic mass-gap bound for the ordinary positive shadow grammar, valid for every fixed positive integer denominator C, including C=211. It applies to arbitrary, potentially aperiodic cost sequences and does not use a fixed modular quotient. The exact block identity, scaled and integer interval bounds, and binary cost bounds in [ShadowGap.lean](ShadowGap.lean) compile locally in Lean 4.36.0-rc2, with only ordinary axioms. The interval counting and asymptotic consequences below are paper proofs, not Lean-checked theorems. They do not settle the three root32 shadow trees.

## Block grammar and exact identity

Use the ordinary rules in [ShadowPeriodicity.md](ShadowPeriodicity.md) (equivalently [ShadowScalar.lean](ShadowScalar.lean) at C=211). Put S=U+2V and w=V-2C>0. Direct edges halve w and add 4C to S. A high edge has cost d>=2, o=(U+V) mod 2, p=2^(d-1), and obeys

    p U'=U+V-C o+p C(2+o),
    2V'+U'=S+C(3d+1).

Consider one high edge followed by t>=0 direct edges, ending at the next high-edge input with mass S_next and right excess h>0. (The direct run need not be maximal: a high edge may be chosen while a direct edge is still available.) Then

    (p-1)S+w+C(2+o)+p C(3d-5-o) = 2p 2^t h,
    S_next=S+C(3d+1+4t).

The final term on the left is nonnegative, since d>=2 and o<=1. An infinite positive path has infinitely many high edges: otherwise its strictly positive integer right excess would be halved forever.

If w<=M, define the real center r=2p 2^t h/(p-1). The exact identity implies

    0 <= r-S <= M/(p-1)+6Cd <= 2^(2-d) M+6Cd.         (1)

Indeed C(2+o)+p C(3d-5-o) <= 3pCd <= 6(p-1)Cd. This proves a one-sided interval restriction, not merely a residue condition. Integer floor(r) satisfies the corresponding exact natural inequality.

## Finite mass-octave covering theorem

Fix natural N,M>=1, let L=ceil(log2(3N)), D=C(7L+1), and assume C(3L+1)<=N, M+6CL<=N. Along any positive ordinary path consider blocks beginning at mass S in [N,2N] for which **both** start and next-high right excess are at most M. Their disjoint mass intervals [S,S_next) have total length at most

    12 M [ 2M + 3C L(L+1) + L D ].                    (2)

Proof. Positivity and 2^d | U+V-Co give d<=log2 S<=L. The immediately post-high mass is at most 2N+C(3L+1)<=3N. Since its excess equals 2^t h and h>=1, t<=L. Thus the mass increment is at most D.

For a fixed d the centers from (1) lie in [N,3N]. Put q=2^t h=(p-1)r/(2p). Since 1/4<=(p-1)/(2p)<1/2, necessarily N/4<=q<=3N/2. As 1<=h<=M, every possible t is at least T=max(0,ceil(log2(N/(4M)))). At each such t there are at most 3N/(2*2^t) candidate positive h. Summing this geometric bound gives at most 3N/2^T<=12M pairs (t,h), hence at most 12M distinct centers for this d. Counting duplicate pairs only increases the upper bound.

Every counted block interval is contained in the real interval [r-E_d,r+D] with E_d=2^(2-d)M+6Cd. Therefore the total measure of the union of such blocks is at most 12M times the sum of E_d+D over 2<=d<=L. Using sum 2^(2-d)<=2 and sum d<=L(L+1)/2 proves (2). Intervals of distinct blocks on one path are disjoint except possibly endpoints, so their lengths sum to their union's measure.

## Consequences for all infinite paths

For every infinite positive ordinary path, infinitely many high-edge inputs satisfy

    V-2C > sqrt(U+2V)/16.                              (3)

Suppose otherwise, so all sufficiently late high inputs have w<=sqrt(S)/16. Their masses increase without bound, and on the octave [N,2N] every block increment is at most D=O_C(log N). The first high mass at or above N is at most N+D: the previous block starts below N, and the same cost bound applies to it. The blocks starting in [N,2N] consequently cover at least [N+D,2N], for all sufficiently large N. The next-high masses are <=2N+D<=3N. With M=floor(sqrt(3N)/16), all such blocks meet the small-excess assumption, and both finite-octave hypotheses hold eventually. But (2) gives a total length at most

    24 M^2 + O_C(M (log N)^2)
    <= (9/32)N + o(N),

contradicting the required N-D. This proves (3), without eventual periodicity, equidistribution or a probabilistic assumption. In particular infinitely many direct runs between consecutive high edges have length less than (log2 S_next)/2+3, because their initial excess is below S_next/2.

Stronger density statement: for every fixed 0<alpha<1/2, among high inputs whose masses lie in [N,2N), the lower limit of the fraction with w>N^alpha is at least 1/2 as N tends to infinity. Set M=floor(N^alpha). Each small-to-small block has mass increment at least 7C, so (2) bounds their count by O_C(M^2+M(log N)^2). The total number of blocks starting in the octave is at least (N-D)/D. The ratio is therefore o(1), since 2alpha<1. Every other block has at least one large endpoint, and a single large endpoint is incident to at most two blocks; at most one such endpoint is just outside the octave. Hence at least half minus o(1) of its high inputs are large. Their preceding direct runs have t<(1-alpha)log2 N when S_next<2N, from 2^t w<S_next/2.

## Relevance and remaining gap

This rules out all putative infinite positive shadow paths whose high-edge inputs eventually stay in a square-root-scale strip, including a class of genuinely aperiodic paths with uniformly near-maximal direct blocks. It also provides an explicit finite mass budget for any path restricted to such a strip across an octave. No uniform right-excess strip is proved for the authentic root32 shadows: high inputs can have excess proportional to their mass. Thus this is a necessary structural obstruction and a possible pruning rule for restricted subfamilies, not a mortality certificate, a precision-budget bound on all branches, or a blank-root decision. In particular it does not supersede the earlier no-uniform-fuel obstruction.

The seven exported algebraic declarations in ShadowGap.lean compile using Lean 4.36.0-rc2 (b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a). Profiles are [propext, Quot.sound] or [propext, Classical.choice, Quot.sound], with no sorryAx. The generic hypotheses are the exact arithmetic equations of the established ordinary grammar; no new source CI or upstream machine-level acceptance is claimed. The counting argument above remains unformalized. BB(6) remains open.
