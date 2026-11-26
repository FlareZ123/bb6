# Grouped positive-token gap inequality for machine #746

**Status:** paper theorem over the existing exact reset arithmetic and periodic rigidity, with the integer segment, product, and exclusion lemmas locally kernel-checked in [GroupedGap.lean](GroupedGap.lean), Lean 4.36.0-rc2. The geometric cyclic-order argument is a paper proof. No authentic blank-root decision is claimed.

## Result

Let a hypothetical infinite periodic successful reset itinerary have a primitive full token period (a,delta) of length L, total valuation A, and total level increment D>0. Its primitive valuation word has length L0, contains t positive entries, and is repeated b times in the full token period, so L=b L0. Let q be the reduced normalized-slope denominator and r the reduced second-coordinate denominator. Use the necessary conditions of [PeriodicBetaSearch.md](PeriodicBetaSearch.md): D<=A, q divides (2^D-1)^2, q/gcd(q,2^D-1)=r/gcd(r,D), and 2^(A+L+D)<3^(A+L).

Then the grouped gap product is

    2^(A+L+D) < 2^L0 q^t.                        (1)

Consequences:

* If t=1, there is no such period, for **any** positive valuation, **any** number of zeros between successive positive valuations, and **any** repetition factor b. The previously excluded single-positive full token period and constant-valuation periods are special cases.
* If t=2, necessarily b<=7, with no restrictions on zero-run lengths or the magnitudes of the two positive valuations. The earlier bound for primitive valuation length two had no intervening zeros.
* For every t, A+(b-1)L0 < (2t-1)D. This is a quantitative necessary constraint independent of the second coordinate.

## Proof of the grouped product

At each of the t positive-token phases of the primitive valuation word, place the phase boundary immediately after the previous positive token. There are b distinct slope states in (1/2,1) at every phase: equality of slopes at one valuation phase would force equality of all future increments by deterministic normalization, contradicting primitivity of the full token word.

The next block consists of m zero valuations followed by a positive valuation a. All zero increments are zero, and their slope map is z -> (z+1)/2. Thus after the m zero tokens, the slope is 1-(1-z)/2^m. The positive token gives the block map

    z' = c(z+C),   C=2^(m+1)-1,
    c=3^a/2^(a+1+m+delta).

There can be at most two consecutive values of delta on the phase's finite slope set: the ratio between the extreme values of z+C is less than (C+1)/(C+1/2)<=4/3<2, and normalization places all outputs in (1/2,1). If both values occur, the lower input slopes use the greater multiplier c and the higher slopes use c/2. The map preserves cyclic order (all high-group outputs precede all low-group outputs).

Use the same circular gaps as in [PeriodicValuationGaps.md](PeriodicValuationGaps.md): ordinary adjacent differences and the boundary gap 2z_min-z_max. Every gap is strictly between 0 and 1; it is N/q with 0<N<q. Associate each gap with its lower endpoint in cyclic order, including the boundary gap with the largest slope. For an ordinary gap, either both endpoints use the same multiplier and the difference scales, or they straddle the seam and the new doubled boundary difference scales with the greater multiplier. For the boundary gap, whether the image is ordinary or remains circular, its new value is the associated endpoint's multiplier times (g+C). In the two-group case this follows from c(z_min+C)-(c/2)(z_max+C)=(c/2)(2z_min-z_max+C); in the one-group case it follows from 2c(z_min+C)-c(z_max+C)=c(2z_min-z_max+C). These formulas also apply when b=1, using its sole gap z.

The gap transitions follow the endpoint permutation. The latter is one full cycle of length t b (since the token period is primitive), so the gaps form a single indexed cycle with exactly t additive events, one per positive phase. Split the gap cycle into t segments, each starting at its additive event and continuing to just before the next. If a segment has accumulated binary exponent B_i and ternary exponent A_i and the initial positive phase has m_i preceding zero tokens, then

    2^B_i N_next = 3^A_i (N_i + (2^(m_i+1)-1)q).

By coprimality, 2^B_i divides the positive right-hand parenthesized integer. Since N_i<q,

    2^B_i <= N_i+(2^(m_i+1)-1)q < 2^(m_i+1)q.

Multiplying over segments proves (1), because sum B_i=A+L+D and sum(m_i+1)=L0. This is the substantive change: counting additive events after grouping zeros replaces L0 factors of q by only t, while preserving the exact binary capacity 2^L0. The arithmetic is checked by segment_bound and product_lt.

## Exclusions

For t=1, q<2^(2D) gives A+L+D<L0+2D, impossible since L>=L0 and A>=D. For any t the same substitution proves A+(b-1)L0 < (2t-1)D.

For t=2, let A0=A/b and S=A+L=b(A0+L0). The first-difference identity gives q<2^D r. Applying (1) gives 2^S<2^(L0+D)r^2. The slope product and 3^5<2^8 yield 5D<3S. Raise the gap bound to the fifth power and cancel 2^(3S) to obtain

    2^(2S)<2^(5L0)r^10.

Since the primitive second-coordinate word has total valuation A0 and length L0, its denominator r divides |2^(A0+L0)-3^A0|. In particular r<max(2^(A0+L0),3^A0). Hence

    2S < 5L0+max(10(A0+L0),16A0).

If b>=8 then 2S>=16(A0+L0), larger than both right-hand terms for A0,L0>0. Contradiction. The entire exponent/cancellation argument is kernel-checked in two_positive_repeat_le_seven.

## Scope

The normalized slope and second-coordinate reductions require an infinite periodic successful itinerary, with no assumption of a blank root. This excludes a larger infinite family of candidate periodic certificates; it does not exclude aperiodic or all multi-positive periodic itineraries. The geometric reduction from slopes to the list of abstract integer segments is not kernel-formalized. All four exported Lean results print only standard axioms, with no sorryAx. The original-source #746 fatal-index cutoff and global BB(6) remain unchanged.
