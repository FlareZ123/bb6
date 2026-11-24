# Exact rank-window carry reduction

This is a size-sensitive reduction of the signed q0 graph from [Q0MacroReduction.md](Q0MacroReduction.md), not an exclusion of the q0 family. The local Lean 4.36.0-rc2 proof [Q0RankBarrier.lean](Q0RankBarrier.lean) imports the exact Q0MacroCore.lean blob 06821faeb7c97a2b6f65adb68cdc2f707dcfa03e, with no stubs. The principal declarations trace_of_formula, near_power, E_bounds, carry_bounds, rolling_div_iff, crossing_iff compile with only propext, Classical.choice and Quot.sound.

## Exact past formula

Use chronological words, with the first digit least significant. For a k-step word w, define M=16^k, D=sum d_i 16^i, L=sum l_i and E=sum (c_i-d_i sum_{j=i}^{k-1} l_j)16^i. A signed trace (p,y) to (P,Y) is equivalent to

    P=p+L, M Y=y+D P+E.

The converse is exact: divisibility of the endpoint formula forces the first division, then induction forces every other division. All coordinates are natural. For all words, 0<=3D<M and -M<15E<2M; append digit d by D'=D+dM, E'=E-l_d D+(c_d-d*l_d)M. The latter coefficient is 0,1,2,2.

If P=aM+b (a,b natural), any strict-interior k-step past implies Y=aD+e for an integer e with 0<=3e<=a+b. This follows from M e=y+bD+E and 0<3y<p. Thus the huge height is a restricted-digit word plus a small correction.

## Exact future strip

The following k steps with digits d_i are described by reading the past digits r_i one at a time in the small recurrence

    q_0=b, e_0=e,
    q_{i+1}=q_i+l_{d_i},
    16 e_{i+1}=e_i+a*r_i+d_i*q_i+c_{d_i}.

At each step the actual rank is aM+q and the height is a times the current rolling k-digit word plus e; drop its first digit and append d. Integrality is equivalent to integrality of the small carry. The bounds q in [b,b+6k] and 0<=3e<=a+q are preserved. A second future block can read the first block's output word as input. The theorem crossing_iff identifies the existence of a strict-interior past and a k-step future at aM+b with existence of two length-k words and a carry trace satisfying the exact initial cone

    0 < M e-bD-E,
    3(M e-bD-E) < aM+b-L.

It is therefore sufficient as well as necessary for signed-graph crossings. It does not assert that a signed path arises from an authentic original blank history.

## All-scale target

For each fixed a,b, the carry coordinates are O(k). The cone condition can also be checked using small signed radix carries (not yet formalized): guess total L, track the prefix cost s, and read coefficients t_i=b*r_i+c_{r_i}-r_i*(L-s). Then B=sum t_i*16^i=bD+E. Compute floor(B/M) and floor((3B+b-L)/M) by Euclidean carries, remembering whether the latter has nonzero remainder. The two inequalities above reduce to comparisons of these carries with e and 3e-a. This permits polynomial-width strip DP for a fixed number of future blocks, rather than enumeration of exponential heights. The all-scale impossibility of sufficiently long strips remains open.

One useful objective is rank barriers: at each scale k find coefficients with adjacent barrier ratios bounded below 2, such that no strict-interior signed trace can pass through any of a*16^k,...,a*16^k+5 with k prior and 2k subsequent steps. Every length-m q0 path starts at p=3m+7 and ends at least p+3m; since increments are 3..6, a barrier within [p+6k, p+3m-12k-5] would contradict the path. This needs a uniform barrier theorem and a separate bounded small-scale closure. Preliminary experiments suggest a=13 is promising but several other coefficients have crossings; neither universal barriers nor any new q0 exclusion are claimed.
