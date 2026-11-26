# No three-token periodic reset itinerary

**Result (26 November 2026).** Every infinite successful #746 reset itinerary with a full period of length three is impossible, including arbitrary zero valuations. Together with [the two-token exclusion](TwoTokenPeriod.md) and [the grouped positive-gap theorem](GroupedPositiveGaps.md), this excludes all full periods of length at most three. The integer lower-bound combination, tail cutoff, exact denominator-cap search and bounded token exclusion are kernel-checked in [ThreeTokenPeriod.lean](ThreeTokenPeriod.lean), Lean 4.36.0-rc2. The connection to the original reset dynamics is a written proof using [PeriodicRigidity.md](PeriodicRigidity.md) and [PeriodicBetaSearch.md](PeriodicBetaSearch.md). This is not a verdict for the blank-root orbit.

## 1. A new lower bound on the beta denominator

Let the three cyclic valuation entries have sorted values a<=b<=c (the chronological order need not be sorted), total A=a+b+c, and total increment D>0. Constant valuation words are already excluded by the grouped positive-gap theorem, irrespective of their full token length. Assume A>=7; smaller totals will be exhausted directly.

The second coordinate y=p/r (r>0, coprime to 6) follows y'=3^v(y+1)/2^(v+1). The three cyclic fixed points have common reduced denominator r, dividing V=3^A-2^(A+3)>0. For A>=7, V>=3^A/2 (verify at 7, then multiply the competing powers by 3 and 2).

At the phase after the largest valuation c, the unreduced absolute numerator is

    U=3^c*(3^(a+b)+2^(v+1)*3^w+2^(a+b+2)),

where (v,w) is either (a,b) or (b,a), as determined by the cyclic order. Since the common cancellation factor V/r is coprime to 3, it divides the parenthesis, which is at most 7*3^(a+b). Thus

    14*r >= 3^c.                                              (1)

The corresponding bound U_i<=7*3^A applies at every phase, so the negative rational beta cycle has x_i=-y_i with 1<x_i<=14.

If a=0, (1) already implies 3^(a+b)<=28*r*2^a. Otherwise all three valuations are positive. Each phase numerator p_i is divisible by 3 to at least the preceding valuation, since its update multiplies by 3 to that power and divides by a power of 2. The two phases immediately after the two largest valuations therefore have numerators both divisible by 3^b. They must be distinct: equality would imply equality of all their future valuation entries by the deterministic rule v=v2(|p+r|)-1, and a nonconstant cyclic word of length three cannot have a smaller period. Hence their difference has magnitude at least 3^b.

For any phase with outgoing valuation v>=a, the recurrence gives

    |p_i+r| = r*(x_i-1) = r*x_(i+1)*2^(v+1)/3^v
             <=28*r*(2/3)^a.

Both p_i+r are negative, so the absolute difference of the selected two numerators is at most this same bound. It follows that

    3^(a+b) <= 28*r*2^a.                                      (2)

Squaring (2), use 2a<=a+b to get 3^(2(a+b)) <= (28r)^2*2^(a+b). Cubing and using 8<=9 gives 3^(4(a+b)) <= (28r)^6. Raising the weaker 3^c<=28r from (1) to the fourth power yields the central bound

    3^(4A) <= (28r)^10.                                       (3)

The integer implication (1),(2) -> (3) is kernel-checked by beta_lower. The rational-cycle argument supplying (1),(2) remains a paper proof. It uses no assumption about a blank root.

## 2. Uniform total-valuation cutoff

Write H=2^D-1 and let q be the reduced normalized slope denominator. The necessary denominator identities q|H^2 and q/gcd(q,H)=r/gcd(r,D) imply r|D*H. The strict slope-band product gives

    3^A < 2^(A+D),    2^(A+3+D)<3^(A+3),    D<=A.

In particular r<=D*H<A*2^D and 8*2^A*r<27*A*3^A, hence 2^A*(28r)<95*A*3^A. Combining its tenth power with (3) and cancelling 81^A yields

    1024^A < (95*A)^10*729^A.

The reverse weak inequality holds at A=303 (integer calculation) and persists, since for n>=303, 30(n+1)<=31n and 729*31^10<=1024*30^10. Theorems tail_bound and valuation_bound check this reasoning. Thus A<=302.

## 3. Sharpening the cutoff to A<=7

Rather than enumerating millions of token triples, use the necessary common denominator cap

    C(A,D)=gcd(|2^(A+3)-3^A|, D*(2^D-1)),   r|C(A,D).

Consequently 3^(4A)<=(28*C)^10 is necessary. For each A, put d0=floor(log2(3^A))+1-A. The two strict band inequalities imply D is d0 or d0+1: the lower one gives D>=d0; the upper follows from 27<32 and 3^A<2^(floor(log2(3^A))+1). The theorem D_choices proves this with Nat.log2, not floating point.

There are just 590 possible cap checks for 8<=A<=302. In every case either a necessary band/increment inequality fails or (28*C)^10<3^(4A). The axiom-free theorem cap_checked evaluates the complete check, and small_total composes the tail and cap bound to force A<8.

## 4. Exact remaining token census

For 0<=v<=7 and 0<=delta<=v use the necessary slope inequalities 3*3^v<2^(v+2+delta), 2^(v+delta)<2*3^v. These give 11 tokens. For each ordered triple, let P_i=2^(v_i+1+delta_i), R_i=3^v_i and

    Q=P1*P2*P3-R1*R2*R3,
    n=R3*(R1*R2+P1*R2+P1*P2),

with cyclic analogues n1,n2. Require all three strict slope bands Q<2*n_i and n_i<Q; Q>0; A<8; D>0. Reduce q=Q/gcd(Q,n). The second coordinate has denominator r=V/gcd(V,U) with V=|2^(A+3)-3^A| and U obtained from the same numerator formula using zero increments. Require q>1, gcd(q,6)=1, q|H^2 and the first-difference denominator equality. None of the 11^3=1331 triples passes. small_checked is axiom-free, and no_small_candidate generalizes this exhaustive computation to arbitrary small-total triples.

Run lean ThreeTokenPeriod.lean with Lean 4.36.0-rc2. The arithmetic exports use only propext, Classical.choice, Quot.sound; the two finite checks are axiom-free. No sorryAx. The initial local source SHA-256 is 89b02f6a7079cac5d8bd1f08d20cfa6e9341e5746c1fa2ec66d6d2017b6a437e.

## Remaining quantifier

This excludes full length-three periodic itineraries, not arbitrary repetition of a primitive valuation word of length three, longer periods, or aperiodic itineraries. The source-to-rational reduction and numerator separation argument are written mathematical derivations, not a single original-source Lean theorem. The authentic fatal-index reachability problem remains open.
