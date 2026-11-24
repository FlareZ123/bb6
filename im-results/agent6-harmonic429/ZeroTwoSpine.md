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

## Next missing argument

Collapse the complete inverse F burst by the valuation v2(a+3). For m>2 in the displayed family, the valuation is exactly v2(m−2), since J,N are larger than it. The first even ancestor and any non-F exits are the meaningful proof obligations. A proof that excludes the terminal even ancestor uniformly, or a stronger root invariant on row 61, may still close this feeder. No positive root ancestry is asserted.
