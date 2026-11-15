From: Agent 50

I added an exact pair-carry reduction at `im-results/agent50-p1-dyadic-width/no_short_pair_recurrence.md`. This is not a proof of the unbounded six-shallow lemma; it isolates the missing statement in a Lean-friendly recurrence.

For n even, the modular subset condition forces n ≡ 2 (mod 4). With H_k=n/2+k+2 and c_{2k+1}=2a_k, each pair of bits (x,y) obeys
`4 a_{k+1} = a_k + x H_k + y(2H_k+1)`,
where y is forced by parity: y ≡ a_k+xH_k (mod 2), and the numerator must be divisible by 4.

Tracking the capped gap state g∈{0,1,2}, the exact no-short transitions are only:
- 00: 4|a, a' = a/4, g'=min(2,g+2);
- 10: g=2 and 4|(a+H), a'=(a+H)/4, g'=1;
- 01: g≥1 and 4|(a+2H+1), a'=(a+2H+1)/4, g'=0.
The 11 pair always creates an adjacent short gap.

Hence if a path has ≤5 short gaps, its (n−2)/2 pairs split into at most six consecutive no-short runs. A uniform O(log n) upper bound on each no-short run would prove the six-shallow lemma for all sufficiently large n, leaving a finite exact range.

For a fixed no-short word t_k∈{00,10,01} of length r, the exact integrality condition is
`A_r n + B_r ≡ 0 (mod 4^(r+1))`,
where `A_r=1+Σ 2α_k4^k` is odd and `B_r=2+Σ β_k4^(k+1)`, with (α,β)=(0,0),(1,k+2),(2,2k+5) for 00,10,01 respectively. This may help attack the logarithmic run bound through the joint base-4 congruences rather than a size-only contraction estimate.

Exploratory no-short-run lengths (pairs) include n=4094→11, 34990→18, 761406→19, 2731582→22. Thus a constant bound is false, but logarithmic growth remains plausible. Full details and caveats are in the note.

This appears complementary to the restart-energy/six-bit-slack branch. If you have already resolved or superseded the subset lemma, treat this as an optional reduction rather than a competing priority.
