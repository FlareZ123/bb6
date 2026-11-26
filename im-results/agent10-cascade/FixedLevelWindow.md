# Linear-size fixed-level inverse cones and exact ray compression for #746

**Status (26 November 2026):** paper theorem over the source-certified exact ResetParent grammar. Arithmetic core [LevelWindowCore.lean](LevelWindowCore.lean) locally kernel-checked on Lean 4.36.0-rc2 (propext, Quot.sound only); full counting and compression theorem not yet source-connected in Lean. [fixed_level_cone.py](fixed_level_cone.py) is an exact compressed enumerator. No blank-root decision follows.

## 1. Statement and coordinates

Let F(k)=4*2^k-k-4. The unique level of h is k such that F(k)<=h<F(k+1); a reset source must have h>F(k). The complete source [FirstInverseComplete.lean](FirstInverseComplete.lean), in the unified form of [PeriodicReset.lean](PeriodicReset.lean), gives

    2^a*(2u+5)=3^a*(h+k+5+8*2^k),  a>=0.

The child's level K>=k by strict growth. Put delta=K-k. Every edge satisfies a<=2*delta: the bands imply (3/2)^a<(4/3)*2^delta, whereas (3/2)^(2delta+1)>(4/3)*2^delta. Thus same-level edges are even. An even edge raises the level by at most one, since u<=8*2^k-3. At a fixed level the unique even inverse doubles the positive deficit T_k-h, with T_k=8*2^k+k. For any fixed source level and valuation, the inverse source is uniquely determined.

For fixed gap g>=1 define

    B=3^(2g), S=bit_length(4B), T=g(S+1),
    M=4g+gS+bit_length(B)+bit_length(T)+1,
    R=M+3, L=2M+2g+12.

For every target u at level N=k+g, k>=L, the number of ancestors in levels k through N, including u, is at most

    (g+1)(N+3)(6R)^g.                                     (1)

Hence the whole fixed-gap cone has O_g(N) vertices, not O_g(N^g). This is an all-target statement. At g=0 there is only a single even ray of at most N+3 vertices.

## 2. One-free-ray lemma

Normalize x=(h+k+4)/2^k, so 4<=x<8. A reverse edge from child level K to parent level k has the exact form

    x_parent=C*x_child-8-epsilon,
    C=2^(a+delta+1)/3^a,
    epsilon=((2/3)^a*(2K+3)+1)/2^k.

Every epsilon is positive and <=(2N+4)/2^k<=2^(-M), since k>=2M and k>=2g+12: 2N+4<=3k+4<=2^floor(k/2), with the latter inequality checked at 12,13 and then by adding two.

**Lemma.** If a real inverse path leaves a node with x>=8-2^(-M) by a level-decreasing inverse edge, every subsequent same-level run has fewer than S edges while the path stays in the window.

Start a parallel ideal path at z=8 using z'=C*z-8. Its error e=z-x>=0 obeys e'=C*e+epsilon. Consider the prefix ending at the first alleged run of S same-level edges, or any shorter prefix. It has at most g level jumps and gS same-level edges. Sum of valuations <=2g, sum of jumps <=g; product of coefficients <=2^(4g+gS). All coefficients exceed 1 on a valid edge, because C*x_child=x_parent+8+epsilon>12 and x_child<8. Thus every subproduct is bounded by that same product. With at most T edges, the error satisfies

    e<=(T+1)*2^(4g+gS-M)<=2^(-bit_length(B)-1)<1/B.

The first jump cannot be even: delta=1 would give ideal z'=24, incompatible with the real band and the error bound. After this first odd edge, write ideal z=P/3^A, where A is cumulative valuation. Its numerator is coprime to 3: starting P=8, each update replaces P by 2^(a+delta+1)P-8*3^(A+a). Thus 1<=A<=2g and z cannot equal 8. Since x<8 and e<1/B, z cannot exceed 8 either. Since z>=x>=4, its deficit from 8 is at least 1/B. Each same-level ideal inverse doubles that deficit, and after S steps the deficit exceeds 4, contradiction. Taking the first violating prefix avoids assuming the desired bound.

## 3. Counting paths

At level l, the reverse even ray from u is h_j=T_l-2^j*(T_l-u), 0<=j<=J, with J maximal subject to every source being in its strict band (j=0 is included even for a fatal target). Its positive normalized deficit (T_l-h_j)/2^l doubles. At the final ray point the deficit is at most 4+(2l+4)/2^l<=5, hence J<=l+2. Call j early when j+R<=J: its normalized deficit is <=5*2^(-R)<2^(-M), so x>=8-2^(-M). Otherwise there are at most R late choices.

A path has m<=g level jumps and m+1 even runs, including its terminal stopping run. The number of jump-label sequences is at most 6^g: total drop d has 2^(d-1) positive compositions, each part delta admits <=2delta+1<=3^delta valuations, and 1+sum_{d=1}^g 3^d*2^(d-1)<=6^g.

Partition by first early crossing exit, or the final run if none. Before that index every exit has at most R choices; at the index itself there are at most N+3. After an early crossing the lemma bounds each following run to fewer than S<=R edges. Thus each label sequence has at most (m+1)(N+3)R^m paths, proving (1). Counting paths avoids reliance on any inverse-tree disjointness assumption.

Linear dependence on N is sharp for fixed g>=1: F(N) has even predecessor at N-1 of deficit 4N+6 from T_(N-1). Subsequent same-level predecessors double it. Every j with 2^j*(4N+6)<4*2^(N-1)+2N+2 is valid, giving N-O(log N) distinct ancestors at level N-1.

## 4. Exact compression

Before the first early exit specify late positions as J-r, 0<=r<R, evaluated concretely. At the early exit use a single free index j; thereafter enumerate bounded run lengths. If there is no early crossing the terminal even ray is the free-index family.

Each inverse operation is affine over the rationals. The resulting heights have form

    h(j)=(P+Q*2^j)/3^A, Q<0,

with integer P,Q, A<=2g and fixed level. For crossing at valuation a, replace (P,Q,D), D=3^A, by

    (2^a*(2P+5D)-(8*2^k+k+5)*D*3^a, 2^(a+1)*Q, D*3^a).

For an even run of length s, replace P by (1-2^s)*T_k*D+2^s*P and Q by 2^s*Q. Because even inverse heights decrease and remain integral, checking the final strict band suffices for all its intermediate edges.

The strict source band is a single integer interval for 2^j; intersect using exact bit lengths. Integrality P+Q*2^j=0 mod3^A is impossible unless gcd(Q,3^A) divides P. After division, either no constraint remains or 2^j=c mod3^e with c a unit. The element 2 generates the units modulo 3^e: order 2 mod3 and v3(2^(2*3^(e-1))-1)=e by binomial lifting. Find the unique j class mod2*3^(e-1) by three-digit lifts. All such moduli are nested, so intersecting constraints retains a single class. The result is an exact arithmetic-progressive family, not an overapproximation.

Explore late exits concretely, early exits symbolically and all post-early runs up to S-1. Every ancestor belongs to exactly one output family: the forward reset is deterministic, h<u forbids cycles, and the early/late partition gives a unique encoding. No iteration over the N-long free index is required to count members or test membership. At most O_g(1) families are produced; integer operands still have O(N) bits. This is not a uniform polynomial complexity bound in g.

## 5. Universal seam-word realization

For every surviving N mod6 in {4,5}, the canonical even spine at K=N-1 is u_j=T_K-(4N+6)*2^j. Consider any fixed finite ideal inverse word starting at z=8 with first edge odd and all subsequent ideal values z'=C*z-8 strictly in (4,8). Let A>=1 be total valuation and d total drop. For every sufficiently large surviving N this word occurs as an authentic reverse path from some u_j. The number of eligible j is

    N/(2*3^(A-1)) + O_word(log N).                         (2)

Restrict to 0<=j<=N-1-ceil(log2(4N+6))-C_word, with fixed C_word large enough to absorb finitely many affine coefficients and minimum band margins. Real rational heights then satisfy every strict band for large N. The terminal rational height's denominator is 3^A; its coefficient of 2^j is -(4N+6) times a power of 2, a unit mod3 since N mod3 is 1 or 2. Its constant numerator is a unit mod3 as well: modulo3 it is a power of 2 times 2*T_K+5=8*2^N+2N+3, nonzero in both surviving sectors. The first odd inverse introduces a factor of 3 in the denominator, and later integer shifts carry it. Therefore terminal integrality selects exactly one j class mod2*3^(A-1). Final integrality implies every prior integrality: a nonzero power-of-3 denominator cannot vanish under multiplication by powers of 2, division by powers of 3, or addition of an integer. The complete grammar gives all genuine edges. The omitted late j number O_word(log N), proving (2).

The ideal tree has arbitrarily deep finite words. From any z in (4,8], choose a>=1, delta>=1 with 12<2^(a+delta+1)z/3^a<16, using density of multiples of irrational log2(3/2) modulo 1. Thus for every m there exists a fixed ideal word of m odd crossings, and **every sufficiently large surviving fatal index has genuine inverse paths with at least m odd crossings**, within a bounded level distance depending on m. This is an all-index obstruction to bounded odd-depth pruning, not a root reachability claim.

For fixed g the ideal tree of drop <=g-1 is finite (a<=2delta; each even ray after the first odd has rational gap >=1/3^(2g)). Distinct words and j give distinct real ancestors by forward determinism. The sum of 1/(2*3^(A-1)) over its nodes is an explicit lower bound on the limiting linear coefficient of the full fatal cone, in addition to the canonical ray coefficient 1. Other initial parents and late exits can add rays, so equality is not claimed. [ideal_seam_tree.py](ideal_seam_tree.py) enumerates the exact weighted tree: drop<=16 has 421194 nodes and mass about 0.51902007.

## 6. Reproduction and scope

Run python3 fixed_level_cone.py 10000 12 --check. Independent enumeration considers every valuation and every possible source level. The compressed count is 15194 ancestors in 332 disjoint families, with counts [1,9986,3329,190,1117,230,202,66,42,18,10,3,0]. Regression with seed746 over 135 targets (fatal, near upper band and pseudorandom; gaps1..9; levels near threshold and 1000/2000) compared 88866 ancestors exactly, no discrepancy. N=100000,g=12 gave 151890 ancestors in 790 families, not expanded for comparison. The million-level timing attempt hit the local command timeout; no result claimed there.

The result provides an exact compression for whole fixed-level cones and an obstruction to universal bounded-depth pruning. It leaves the authentic root and BB(6) unresolved. Use the compression within growing-gap rooted arguments rather than treating individual ray nodes as separate proof tasks.
