# Branch-9 zero-two feeder: unbounded exact F-only inverse spines

**Result:** the current necessary-residue sieve cannot reject every diagonal zero-two feeder at any parameter-independent finite inverse depth. For every depth d and positive integer r, choose m=2+2^(d+6)r, J=4m+2, N=8·2^J+J−11. The genuine upper-boundary predecessor of the candidate zero-two feeder has at least d exact inverse F edges, and each vertex passes every test in Agent 30's side_branch_sieve.js. This is an obstruction to that proof method, not a rooted halting or nonhalting result.

## Proof and relevance

Write the feeder as (0,z), where z+48·2^J+3J=12·2^(N+2)+36. Its upper-boundary predecessor is (a,2a+2), with

    a+3 = 12·2^N − 12·2^J − 3(m−2).

For the chosen congruence class, e=d+6≤J<N, and a+3=2^e c for a positive natural c. At each inverse F step the predecessor is ((a−3)/2,a+b); these are genuine positive-counter source edges. The first coordinate after i inverse steps is

    a_i = 2^(d+6−i)c−3.

Thus a_i≥61 and a_i=61 mod64 for all 0≤i≤d, regardless of b_i. The row a=61 mod64 has a%8=5, a%16=13, a%32=29, so the entire current residue predicate accepts all b. This also lies in the previously allowed upper-boundary row a%16=13 and m%32=2.

A whole infinite class of genuine parameter values escapes each finite depth. Even exhaustive residue-class enumeration with the present predicate cannot terminate with an empty class at uniform finite depth. This does not contradict rejection of a finite range of m using a depth depending on m. The inverse chain is exact in natural coordinates; it does not rely on replacing the enormous powers by signed representatives.

## Proof status

[ZeroTwoSpine.lean](ZeroTwoSpine.lean) imports the full unchanged repository BB429Rank.lean (blob 5a93ba2d833ca375478f1183f45712a34f299f19). Locally compiled using Lean 4.36.0-rc2, with standard axioms [propext, Classical.choice, Quot.sound] for arbitrary_depth and congruence_spine, [propext, Quot.sound] for row61_necessary. The necessary predicate directly transcribes the JS filter, rather than proving all blank-root states satisfy it. The exact edges use the repository accelerator; upstream raw-TM blank correspondence is not needed for this negative result.

Reproduce from this directory with LEAN_PATH=.:../agent5-429-rank; compile BB429Rank.lean to .olean, then lean ZeroTwoSpine.lean.

## Exact valuation-dependent cover

The arbitrary-depth obstruction motivates a complete compressed inverse F burst, proved in [ZeroTwoEndpoint.lean](ZeroTwoEndpoint.lean), with actual blank-root alternatives in [ZeroTwoRootCover.lean](ZeroTwoRootCover.lean). Suppose a+3=2^k c, c>=9 odd, k>=4, and the starting upper boundary is U=(a,2a+2). At inverse index i<=k,

    a_i = 2^(k-i)c-3,
    2a_i+b_i+3i = 4a+2.

Every F edge along this path is exact. If U is rooted (some run from (0,0)), either the endpoint at i=k is rooted or a genuine S-side parent p=(x,y) enters one of the intermediate states. The side exit necessarily has i<k, i mod4=2, and

    4x+26=4a_i+b_i,  2y=b_i+4,
    2x+21=y+2*2^(k-i)c.

The complete rooted endpoint is even, so BB429Even16.rooted_even_sixteen forces precisely these necessary pairs (k mod16,c mod8):

    (0,1), (4,7), (8,5), (12,3).

[ZeroTwoDiagonalCover.lean](ZeroTwoDiagonalCover.lean) specializes this to the actual diagonal feeder, m=2+2^k*r with r odd and k>=4. It proves a+3=2^k*c for some odd c>=9 with c+3r=0 mod8; hence k is indeed the valuation of a+3. Therefore the necessary disjunction for genuine rooted upper ancestry is a rooted S exit or the four endpoint pairs (k mod16,r mod8):

    (0,5), (4,3), (8,1), (12,7).

This is an infinite-parameter reduction, not a sieve restricted to a fixed number of inverse steps. It does not exclude the remaining four endpoint pairs or any asserted S exit, the odd-reset alternative, m=2 or k<4. In particular the diagonal family is still open.

All three new modules compiled locally in Lean 4.36.0-rc2 with the complete unchanged BB429Rank, BB429Mod8, BB429RootEven8, BB429NoThree and BB429Even16 dependencies. Exact new source blob hashes: ZeroTwoEndpoint 9099f39948d56598e5d650c014b1cba2fb4f048d; ZeroTwoRootCover ce1244819db07f40321d1b981b1c845950957923; ZeroTwoDiagonalCover 8f25391d0d7f1152df28a92fcdba746698b4b6c7. Each exported theorem has only standard logical axioms. No new CI claim. The root cover uses the source theorem BB429Even16.rooted_even_sixteen rather than assuming soundness of the copied sieve.

## Next missing argument

Exclude every genuine S side exit and strengthen the endpoint restrictions to close all remaining classes. For i=4l+2, write A=2^k c and B=2^(k-i)c. Then the exact S parent has x=A+B/2-12-3l, y=2A-B-3-6l. This is the previously studied PowerMinusThree side line; when k-i is sufficiently large, existing source-verified exclusions transport to these parameters. Do not restart an independent fixed-depth sieve. The remaining near-end cases and arbitrary high valuation need a genuine root-history invariant. No positive root ancestry is asserted.
