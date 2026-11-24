# Exact unit-cost renewal of the P1 reverse-parent dynamics

**Status:** mathematical intermediate result, 24 November 2026. [ReverseUnitMap.lean](ReverseUnitMap.lean) is a standalone Lean 4.36.0-rc2 kernel proof of the scalar unit embedding, converse guarded-prefix reconstruction, and exact word identity. The rational renewal and denominator-growth theorems below are paper proofs with exact-integer reproducible certificates in [reverse_unit_renewal.py](reverse_unit_renewal.py). The original-source scalar reverse equations are those in [dyadic_euclidean_249_343.md](dyadic_euclidean_249_343.md); their complete source connection is not re-proved here. No blank-root or BB(6) decision is claimed.

## 1. A deterministic unit-cost map

In the previous reverse-parent coordinates (D,N,m), set d=D/2, q=(N+1)/2 (the lower-case d here is **not** the original source right counter). One source-parent candidate of cost k becomes

    q' = q+k, d' = 2^k d-q', m'=m-k,
    1 <= k <= m,  q' <= 2^k d <= 2q'-8.

The original counters are right=2d+1, left=2(q-d-4). The source parity condition is q-d even. It is preserved at any parent event, since q'-d'=2q'-2^k d is even.

Instead of locating the next k, use the unit map

    q_j = q+j,
    x_j = floor(2d_(j-1)/q_j) in {0,1},
    d_j = 2d_(j-1) mod q_j = 2d_(j-1)-q_j x_j.

It preserves 0<=d_j<q_j. A legal scalar parent is exactly the first subsequent one-bit provided the resulting d_j has the upper margin d_j+8<=q_j and cost remains available. Indeed, if some i<k already crossed, then 2^k d >= 2^(k-i)(q+i) >= 2(q+k)-2, contradicting the upper margin of a legal k. At the first crossing there are only zero bits before it, so the result is 2^k d-(q+k). In applying the original source relation one must also retain its right-counter guard; all the renewal intervals below have d_j>=2 throughout, so the original right counter is at least five and that guard is safe. At a final root, d=1 is permitted as a terminal parent.

Consequently a source path from a restart to the critical root must map to the single unit iteration from (q_R,d_R) for exactly m_R units, ending at d=1, and its last bit must be one. This is a necessary condition even when the relaxed map passes through forbidden states. It is not a certificate of root ancestry unless all the source event guards hold.

For the actual two restart progressions, with P=2^n,

    q_R = 7P-14u+n,
    d_R = (18P-196u+14n+48)/98,
    m_R = 14u-2n-3,
    q_R+m_R = 7P-n-3.

## 2. Exact n-bit renewal lemma

Write the starting integers of a block as

    q = A P + a, d = A P r + b, P=2^n,

where A>0 is a fixed rational, 0<r<1 is a non-dyadic rational, a=O(n) and b=O(n^s) for some fixed s>=1. For the first j unit bits put

    U_j = sum_(i=1)^j x_i 2^(j-i),
    V_j = sum_(i=1)^j i x_i 2^(j-i),
    u_j = U_j/2^j, v_j = V_j/2^j.

Unrolling the exact unit map gives

    d_j = 2^j d - q U_j - V_j.                         (1)

Let mu(r)=sum_(i>=1) i r_i 2^(-i) be the weighted moment of the canonical binary digits of r. Define the rational

    T = P r + (b-a r-mu(r))/A = (d-a r-mu(r))/A,
    rho = {T}.

Suppose the denominator of r divides a fixed Q, and rho is nonzero with denominator dividing a fixed R. These denominator bounds must be independent of n, though r, rho, a and b can vary with n. For all sufficiently large n (uniformly with those bounds and the O-constants),

    U_n = floor(T),                                     (2)
    d_n = P d - q floor(T) - V_n = A P rho + b_new,
    |b_new| = O(n^(s+1)).                               (3)

Moreover every intermediate unit state of this block, including every one-bit event, satisfies 2 <= d_j <= q+j-8.

**Proof.** At j=n, equation (1) and 0<=d_n<q+n, 0<=u_n<1, 0<=v_n<2 imply

    |u_n-r| <= (|b|+|a|+2+(q+n)/P)/(A P) = O(n^s/P).

Choose K=n-O(log n) with 2^(-K)/Q greater than this bound, and 2^K(|b|+|a|+2) <= AP/(4Q); both conditions follow by subtracting a sufficiently large constant from n-ceil(log2(n^s)). Since r is non-dyadic with denominator dividing Q, its distance from every multiple of 2^(-K) is at least 1/(Q*2^K). Thus u_n and r have the same first K binary digits. Their tails are bounded by

    |r-u_n| <= 2^(-K), |mu(r)-v_n| <= (K+2)2^(-K).

Rearranging (1) yields

    d_n = AP(T-U_n) + E,
    E = P[a(r-u_n)+mu(r)-v_n], |E|=O(n^(s+1)).

Because 1/R<=rho<=1-1/R and AP/R eventually exceeds |E|+|a+n|, any integer U_n other than floor(T) would make d_n negative or at least q+n. This proves (2) and (3).

For j<=K, the exact prefix is U_j=floor(2^j r), giving

    d_j = AP{2^j r}+2^j(b-a u_j-v_j).

The two rational phase margins are at least AP/Q; the error is at most AP/(4Q). For j>K use U_j=floor(T/2^(n-j)), since U_j is the prefix of floor(T), and rewrite (1) as

    d_j = AP {T/2^(n-j)} + E_j,
    E_j = 2^j[a(r-u_j)+mu(r)-v_j].

The common first K digits imply |E_j|<=P(|a|+K+2)2^(-K)=O(n^(s+1)). The phase is nonintegral with denominator dividing R*2^(n-j), so both margins are at least AP/(R*2^(n-K)), which grows exponentially divided by a fixed polynomial. This dominates both the error and |a|+n+8, proving the complete safety assertion. QED.

This is an exact block accelerator: the bits of floor(T) are the whole block. The weighted digit integer V_n is computable by binary masks. In the code, weighted_word sums the contribution of each bit of the exponent index; it uses O(log^2 n) shifts and masks on O(n)-bit integers, rather than n modular steps. Computing mu(r) uses the rational periodic formula below. Separation inequalities are checked before returning an endpoint.

## 3. Exact first renewal in both progressions

Using (n,u) from [fourth_edge_terminal_survivors.md](fourth_edge_terminal_survivors.md), the two initial values are

| family | A | r | a | b |
|---|---|---|---|---|
| I | 3584/529 | 491/21952 | n+14*636/1058 | n/7+24/49+2*636/1058 |
| II | 3584/599 | 141/21952 | n+14*712/1198 | n/7+24/49+2*712/1198 |

Both binary expansions have preperiod 6 and period 147. Their weighted moments, computed by exact geometric sums, are respectively

    mu_I = 6111846786571934437162009701224629559707294979 / 39962935395766876669632007144585863818716905248
    mu_II = 2210352705625301289067294318160955170791534925 / 39962935395766876669632007144585863818716905248.

Let Q1=71613580229214242991980556803097867963140694204416. As n ranges over the two specified progressions, the first post-shadow phase is **exactly**

    rho_I(h) = {20013775836248574773416784117434897071012058217091/Q1 + 71731 h/100352},
    rho_II(h) = {29332545262092636321770706426635052127421016820935/(Q1/2) + 78165 h/100352}.

These formulas follow by substitution in T: the fractional part of 2^n r is constant along each progression because the step is a multiple of 147, and the affine-in-n coefficient is (1/7-r)/A. Each phase has exact period 100352 in h. The common denominator Q1 has 166 bits and v_127(Q1)=1. The two base reduced denominators contain 127, and the increments have denominator prime to 127; hence every rho has exact denominator valuation v_127=1, and in particular no rho is zero. The odd part of Q1 has order dividing 7203, with 127 not dividing 7203.

For clarity the first renewal holds for **every h>=0**, not just eventually. Indeed 5<A<7, 0<a<2n, 0<b<n, (q+n)/P<8, so |u_n-r|<n/P. Take K=n-ceil(log2 n)-16. Both r have denominator 21952<2^15, so this K gives a common prefix and |E|<2^19 n^2. The early margin is at least 5P/21952-4P/65536>P/8192. The late margin before subtracting the error is at least 5P/(Q1*2^(n-K))>5P/(2^183 n). For n>=5362, P>2^204 n^3 (use n<=2^(n/4) for n>=16), so the endpoint and all intermediate margins in section 2 are sufficient, including the eight-unit upper guard. Thus the first n bits and post-shadow endpoint follow from (2) and (3) for the entire progressions.

## 4. Denominators grow by a factor of 127 at every renewal

For a rational r with binary preperiod e, write its tail as t in (0,1) with odd denominator. Choose any period L of t, M=2^L-1, and let w=M t be its repeating binary word. If W is that word's weighted integer (indices 1 through L), then

    mu(t)=(W+L t)/M.

This follows by summing the periodic weighted series: the weight in block j is the original weight plus jL. The preperiod contributes a dyadic rational and the tail contributes 2^(-e)(e t+mu(t)). Hence if the denominator of r divides Q and L=ord_(Q_odd)(2), the denominator of mu(r) divides Q M.

The following induction is independent of any numerical trajectory. After the first renewal use the common Q1 above. Suppose at block i>=1 that all phases have denominators dividing Qi with exact 127-valuation i, that v_127(Qi)=i, and that Li=ord_(Qi_odd)(2) has valuation i-1. Since ord_127(2)=7 and 2^7-1=127, the usual elementary lifting-of-exponent identity gives v_127(2^Li-1)=i. In the formula for mu(t), Li*t has valuation -1 whereas W is an integer. Consequently v_127(mu(t))=-(i+1). Adding the preperiod contribution cannot change this, because e*t has valuation at least -i and powers of two are 127-units. Thus v_127(mu(r))=-(i+1).

At the next renewal, T=(d-a r-mu(r))/A, where d is integer, a=q-AP has denominator dividing 529 or 599, and A has numerator 3584, all 127-units. The term a r has valuation at least -i; the weighted moment has strictly smaller valuation. Therefore **the new rho={T} has exact denominator valuation i+1**. It cannot be zero.

A uniform next common denominator is

    Q_(i+1) = 3584 Qi (2^Li-1) / 127^(i-1).

The unrestricted denominator bound before division is obtained from the weighted-moment formula and (d-a r-mu)/A; the division is justified by the exact valuation i+1 just proved. For every odd prime ell other than 127 dividing this next denominator, the order of 2 modulo ell divides Li: ell is already a factor of Qi, a divisor of 2^Li-1, or the prime 7, which already divides Q1. Raising ell to higher powers only multiplies its order by an ell-power, so the 127-valuation of its order is at most i-1. The 127-primary order at exponent i+1 is exactly 7*127^i. Taking the least common multiple gives v_127(L_(i+1))=i, completing induction. The base holds because 2^7203=1 mod Q1_odd and 127 divides Q1 exactly once. All denominators and periods in this induction are fixed for a fixed block index, independent of n and h. They can grow extremely quickly; this is not a practical all-block computation.

## 5. Consequence: superlinear locally legal reverse cost

**Theorem.** For each fixed integer B>=1, there is a threshold N_B such that every member of either restart progression with n>=N_B has a locally legal scalar reverse-parent prefix of cost at least Bn-O_B(log n). In particular the maximum locally legal reverse-prefix cost divided by n tends to infinity along both progressions. No uniform O(n) reverse-cost cutoff can eliminate all these prepared restart states.

**Proof.** The first block was proved uniformly above. For each fixed subsequent block i, its start has q_i=AP+a_i, a_i=a_0+in=O_i(n), and d_i=AP r_i+b_i with b_i=O_i(n^(i+1)). Section 4 gives uniform finite denominators and nonzero next phase; apply the renewal lemma inductively for sufficiently large n. All B blocks have complete safety margins at every unit state. The actual source cost budget m_R is a positive linear function of P plus O(n), so eventually exceeds Bn. Concatenate all one-bit events via the scalar embedding in section 1, preserving source parity and right-counter guards. In the last block, the first n-O_B(log n) bits match the fixed-denominator non-dyadic rational r_(B-1). The binary preperiod and period are uniformly bounded, and every period contains at least one one-bit. Therefore the last parent event is at or after Bn-O_B(log n) (the trailing zeros can be a partial parent edge). For any desired ratio C choose fixed B>C. QED.

This is a genuine obstruction to solving the missing ancestry with a uniform linear-cost reverse-prefix search. It does not establish an infinite trajectory at any fixed n: m_R is exponential in n and the threshold N_B may grow very fast in B. It also does not supersede the root-prefix carry cylinders, which exclude ancestry from the opposite end. The next decisive target is an invariant or certified shortcut valid when the unit cost is comparable to P, rather than another bounded-n trace.

## 6. Reproduction and precise proof boundary

Run python reverse_unit_renewal.py (standard library only). The base first blocks are compared to independent literal unit iteration; the h=1 second blocks use the exact separation certificate rather than an enormous scan. Output:

| family, h | n | block | exact one-bit events | last event within block | denominator valuation v_127 |
|---|---:|---:|---:|---:|---:|
| I, 0 | 5362 | 1 | 2667 | 5362 | 1 |
| II, 0 | 9538 | 1 | 4734 | 9535 | 1 |
| I, 1 | 600418 | 1 | 298163 | 600418 | 1 |
| I, 1 | 600418 | 2 | 300677 | 600415 | 2 |
| II, 1 | 712786 | 1 | 353967 | 712784 | 1 |
| II, 1 | 712786 | 2 | 356622 | 712783 | 2 |

An additional independent literal comparison for family II, h=0, block 2 also passed: 4828 events, last offset 9537, phase denominator 7357 bits, valuation 2.

The proof of the n-bit shortcut is exact; for blocks beyond two the paper theorem asserts eventual uniform safety, not these particular numerical thresholds. The Lean module proves the arbitrary-depth scalar embedding, word_identity, path_run, first_cross_edge, and guarded_prefix; axioms are [propext, Quot.sound] or [propext, Classical.choice, Quot.sound], with no sorryAx/native_decide. No claim that the rational-moment estimates and p-adic induction are kernel checked, or that the original source wrapper has been compiled.
