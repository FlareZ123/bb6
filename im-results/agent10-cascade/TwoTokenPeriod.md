# No two-token periodic reset itinerary

**Result (26 November 2026):** no infinite successful #746 reset itinerary can have a full periodic token word of length two, for arbitrary valuations and increments. The length-one case is covered by the existing grouped-gap theorem. This extends the earlier finite-D scan to an unbounded word family. The integer inequalities reducing the search to A<=44 and the exhaustive finite check are kernel-checked in [TwoTokenPeriod.lean](TwoTokenPeriod.lean) under Lean 4.36.0-rc2. The reductions from the reset recurrence to the arithmetic hypotheses are paper-level, using the prior [rigidity](PeriodicRigidity.md) and [second-coordinate](PeriodicBetaSearch.md) results. No rooted nonhalting claim follows.

## Unbounded reduction

Write the two tokens as (a,d),(b,e). Let A=a+b, D=d+e>0. If one valuation is zero, the primitive valuation word has only one positive entry, already impossible by [GroupedPositiveGaps.md](GroupedPositiveGaps.md). Thus a,b>0.

Let y=p/r denote the reduced second coordinate at either phase. Both phase denominators equal r. The respective numerators before reduction of the fixed-point equations for y'=3^a(y+1)/2^(a+1) are

    U1=3^b(3^a+2^(a+1)),
    U2=3^a(3^b+2^(b+1)),

and their common signed denominator is 2^(A+2)-3^A. The absolute denominator V is coprime to 6. Let g=V/r be the common cancellation factor. As g is coprime to 3 and divides both numerators, it divides 3^m+2^(m+1) for m=min(a,b), so g<=3*3^m.

For A>=6, 2*2^(A+2)<=3^A. This holds at 6 and propagates by multiplying the two sides by 2 and 3 respectively. Consequently V>=3^A/2. Since V=r*g and 2m<=A,

    3^A <= 6*r*3^m,
    3^A <= 36*r^2.

These inequalities are kernel-checked by denominator_dominates and beta_lower.

Set H=2^D-1. The reduced slope denominator q divides H^2 and satisfies q/gcd(q,H)=r/gcd(r,D). For any prime, subtracting the smaller valuation from the valuation of q shows q/gcd(q,H) divides H; hence r<=D*H. Also D<=A and the slope product gives 2^(A+2+D)<3^(A+2). Therefore

    r < A*2^D,
    4*2^A*r < 9*A*3^A.

Squaring and applying 3^A<=36*r^2 yields

    4*4^A < 729*A^2*3^A.

The reverse weak inequality holds at A=45, and for every larger A by 3*(A+1)^2<=4*A^2 (valid for A>=7). This is a contradiction. Thus A<=44, including A<6 automatically. The Lean theorems tail_bound and valuation_bound verify this argument without logarithms or floating point.

## Exact bounded exhaustion

For each positive a<=44 and 0<=d<=a the strict slope band 1/2<z,z'<1 requires

    3*3^a < 2^(a+2+d),
    2^(a+d) < 2*3^a.

There are 62 such tokens. For each ordered pair, set P1=2^(a+1+d), P2=2^(b+1+e), R1=3^a, R2=3^b. The two slope fixed points have common denominator Q=P1*P2-R1*R2>0 and respective numerators n=R2*(R1+P1), n1=R1*(R2+P2). Require Q<2n, n<Q, Q<2n1, n1<Q, A<45, D>0. Reduce q=Q/gcd(Q,n) and require q|(2^D-1)^2.

The exact Lean Boolean check enumerates all 62^2=3844 ordered pairs and returns true for the assertion that none passes. The theorem no_candidate generalizes this finite computation to every pair satisfying the admissibility and A bounds. check_all is axiom-free (decide +kernel); the inequality and generalization theorems use only propext, Quot.sound, and, for valuation_bound, Classical.choice. Run lean TwoTokenPeriod.lean.

## Scope and remaining problem

This closes full token lengths one and two without a valuation cap. It does not close arbitrary primitive valuation length two repeated b>1 (the grouped-gap bound limits b to seven), full words with two positive entries separated by zero runs, or other longer periodic or aperiodic possibilities. The authentic #746 orbit and BB(6) remain undecided.
