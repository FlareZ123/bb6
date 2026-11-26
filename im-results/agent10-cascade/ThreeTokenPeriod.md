# No full three-token periodic reset itinerary for machine #746

**Result.** Extending [TwoTokenPeriod.md](TwoTokenPeriod.md), no successful infinite #746 reset itinerary can have a full token period of length three, with arbitrary valuations (including zeros) and increments. The new ingredient is a lower bound on the denominator of the negative second-coordinate cycle from the minimum separation of distinct 3-adically divisible numerators. The arithmetic inequalities, denominator-cap finite check, and final token finite check are Lean-kernel verified in [BetaThreeBridge.lean](BetaThreeBridge.lean) and [ThreeTokenPeriod.lean](ThreeTokenPeriod.lean), Lean 4.36.0-rc2. The connection to the exact original reset grammar remains the paper-level periodic rigidity reduction. No authentic blank-root halt/nonhalt decision is claimed.

## 1. Negative second-coordinate states

Let the three valuations be sorted as a≥b≥c≥0 (their chronological order is arbitrary), A=a+b+c, and D the total level increment. The constant-valuation case is already excluded by [GroupedPositiveGaps.md](GroupedPositiveGaps.md). Otherwise the valuation word is primitive of length three. Its rational second-coordinate orbit y=p/r has three distinct phases because its next valuation is determined by v2(|p+r|)-1. The reduced odd denominator r is the same at every phase.

Assume A≥7. Then R=3^A≥2P, where P=2^(A+3); this follows at A=7 and propagates by multiplication. The cyclic y equation has positive translation numerator and negative denominator P-R, so all y_i<-1. Write u_i=-p_i>r. For a chronological phase with valuation e, its successor satisfies

    3^e (u_i-r) = 2^(e+1) u_(i+1).

Each u_(i+1) is divisible by 3^e. Substituting the three inverse equations in a cycle yields

    R u_i = (R + P_i R_(i+1) R_(i+2) + P_i P_(i+1) R_(i+2)) r + P u_i,

where R_i=3^e, P_i=2^(e+1). Since P_i≤2R_i and R≥2P, this implies u_i≤14r at every phase (phase_bound).

Choose the phase preceded by a maximum valuation a. Then 3^a≤14r. Choose the two phases preceded by a and b. Their distinct numerators are both divisible by 3^b. Since each outgoing valuation is at least c, their inverse equations imply

    3^c (u_i-r) ≤ 28 r 2^c.

The nonzero difference of these two numerators is at least 3^b and is no larger than the larger u_i-r. Consequently 3^(b+c)≤28 r 2^c (close_to_r, close_pair). This argument applies also if two valuations are equal, provided the word is not constant, and if c=0.

If 5a≥2A, the first bound gives 3^(2A)≤(14r)^5. Otherwise 5(b+c)>3A and b≥c; square the second bound, replace 2^(2c) by 2^(b+c), raise to the fifth power, and use monotonicity of (9/2)^s to obtain

    3^(6A) ≤ (28r)^10 2^(3A).

## 2. Unbounded cutoff

From the existing first-difference denominator identity and q|(2^D-1)^2, we have r≤D(2^D-1), D≤A. The slope product gives 2^(A+3+D)<3^(A+3). Hence

    8*2^A*r < 27*A*3^A.

Combine this strict upper bound with the first or second lower bound above to obtain, respectively,

    8^5*32^A < (378*A)^5*27^A,
    8^10*128^A < (756*A)^10*81^A.

Both reverse weak inequalities hold at A=300. They propagate for n≥300 because 32(n+1)≤33n and 27*33^5≤32*32^5, 81*33^10≤128*32^10. Thus A<300. The theorems valuation_bound and beta_upper are exact integer proofs, and the A<7 branch automatically satisfies the cutoff.

## 3. Exact aggregate and token exhaustion

Put H=2^D-1, g=gcd(P*2^D-R,H^2), C=gcd(|P-R|,D*(g/gcd(g,H))). The slope denominator q>1 divides g; the first-difference identity and gcd-quotient monotonicity give r|C, as in [PeriodicBetaSearch.md](PeriodicBetaSearch.md). Use the inequalities 3^A<2^(A+D), 2^(A+3+D)<3^(A+3), and, for A≥7, either lower bound with C replacing r. The complete kernel computation check_pairs examines 45,150 aggregate pairs 0≤A<300, 0≤D≤A and leaves only the possible pair A=6,D=5. The theorem aggregate_only incorporates the unbounded cutoff and cap monotonicity.

For that pair, all tokens have 0≤valuation≤6 and 0≤increment≤valuation. There are 28 such tokens; the kernel computes all 28^3=21,952 ordered triples. For chronological tokens (a_i,delta_i), put P_i=2^(a_i+1+delta_i), R_i=3^a_i, Q=P_1P_2P_3-R_1R_2R_3. The cyclic slope numerator at phase zero is

    n_0=R_3*(R_2*(R_1+P_1)+P_1P_2),

and the other phases are its cyclic rotations. Require A=6,D=5, Q>0, Q<2n_i<2Q for all phases, and q=Q/gcd(Q,n_0)>1 dividing 31^2. No triple survives. The theorems check_tokens and no_tokens certify that computation without native_decide or additional axioms.

## 4. Reproduction and boundary

Run lean BetaThreeBridge.lean and lean ThreeTokenPeriod.lean. Both compiled locally under 4.36.0-rc2. The two exhaustive theorems have no axioms; every other exported theorem has only standard axioms (propext, Classical.choice, Quot.sound). All arithmetic is exact. Full token lengths 1, 2 and 3 are now excluded without a valuation cutoff. The result does not rule out longer periods or aperiodic itineraries, and no new global BB(6) upper bound follows. The close-numerator inequality may generalize to larger negative beta cycles, but the quantitative exponent comparison for three phases is specific to their total valuation distribution.
