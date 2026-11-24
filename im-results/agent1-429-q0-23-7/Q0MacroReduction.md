# #429 q0: exact signed four-step macro reduction

## Theorem and proof status

For a genuinely reachable q0 target satisfying n=23+32u, a+24u+19=13*2^n and b+13=2a, a necessary condition is a length 8u+5 path in a four-branch arithmetic graph starting from (p,y)=(24u+22,6u+4). Each edge selects d in {0,1,4,5} with y+d*p+c divisible by 16 and updates

    p' = p+l,   y' = (y+d*p+c)/16.

| d | inverse word | l | c |
|---|---|---|---|
| 0 | FFFF | 3 | 0 |
| 1 | FSFF | 5 | 6 |
| 4 | FFFE | 4 | 18 |
| 5 | FSFE | 6 | 32 |

The strict interior 0<3y<p is preserved. Path existence is necessary for blank reachability and sufficient for a prepared-state ancestry, as proved by the exact converse below.

Q0MacroCore.lean contains the full formal derivation with an explicit Source interface, and Q0MacroCheck.lean proves soundness of a purely Boolean recursive cover of dyadic parameter cylinders. Both compiled locally using Lean 4.36.0-rc2, with only standard axioms. Q0MacroFinite.lean proved cover 43 0 0 1000000 = true, with no axioms, in 12.7 seconds locally. Q0MacroSource.lean instantiates Source from BB429NewResidue and BB429RootEven8. The adapter compiled locally against exact extracted original declarations (BB429.next/run, Allowed and its rooted proof, exact odd/even inverse and rooted predecessor proofs, rooted_positive_even_eight); no stubs or added axioms. The full repository-file CI build has not been performed. The theorem q0_excluded_below_million excludes genuine accelerator-root reachability for u<10^6. No raw machine #429 decision follows yet.

## Derivation

Use rank R=2a+b. Ordinary inverse F,S,E decrease it by 3,11,7 respectively, all congruent to 3 mod 4. The positive-even rooted second-counter invariant implies any phase R != 2 mod 4 with positive a must have odd a. A sufficiently large phase-3 state must take F, then F/S, then F, then F/E. The next phase-3 state has a+3 divisible by 4, by one more F predecessor and its phase-0 parity. For x=(a+3)/4 and r=(R+1)/4, the four macro words give

    r' = r-l,   16x'+c = x+d*r,   x <= 16x'.

Q0MacroCore.macro_back proves this, including every small-counter guard under x>=400. To transfer an actual positive ancestry, suppose x+y and r+p are multiples of 16^m, with x>=25*16^m. Then one actual macro implies an integral signed macro, leaves the two new sums divisible by 16^(m-1), and leaves x'>=25*16^(m-1). Induct. For q0, m=8u+5 and n=4m+3; initially

    x+y=26*16^m, r+p=104*16^m, x>=25*16^m.

Therefore the complete length-m signed path is forced. This eliminates the enormous exponential counters without using any unproved residue tests or assuming a particular inverse word. No arbitrary fixed inverse-depth cap is used.

## Exact converse and rooted endpoint

[Q0Converse.md](Q0Converse.md) proves the four-digit path lift back into the actual accelerator, with exact branch guards. A path of length m=8u+5 ending at (P,Y) with little-endian digit polynomial D reconstructs a prepared ancestor in shifted coordinates X,R with R+P=104*16^m and X+Y=26+104*D; its actual 4m-step run returns the q0 target. Under Source Rooted the target is rooted iff one such endpoint is rooted. Signed path existence alone does not imply blank reachability. The endpoint rank window has width 12m, suggesting direct blank-orbit analysis.

## Adaptive cover

If u = r mod 2^e, a signed path from u of length k=min(floor((e+1)/4),8r+5) implies a path from r of that length. The two initial counter differences are nonnegative multiples of 16^k, and the divisibility transfer works by induction on k. The Boolean function cut e r checks that no such path exists. The cover recursively splits a cylinder into its two children only if the current cut fails and the interval is nonempty. Thus the checker is sound for an entire interval, using no giant counters or individual u enumeration.

Python macro_cover.py independently computes the cover. For N=10^6 it visits 26,741 nodes, with 5,559 cut leaves, 7,812 empty leaves and maximum e=43; there are zero unresolved leaves. For N=10^9 it visits 878,771 nodes, 171,826 cut leaves, 267,560 empty leaves and maximum e=67; zero unresolved leaves. The latter is computational evidence, not a kernel certificate yet. Exact Python counts use cut tests only at e=3 mod 4 (the available depth changes there).

## Structural restrictions (Agent 6)

[Q0Aperiodic.md](Q0Aperiodic.md) proves that strict-interior vertices have unique predecessors and that no infinite strict-interior path can have an eventually periodic digit itinerary. The Lean proofs are in Q0SlopePacking.lean and Q0Aperiodic.lean, compiled locally against exact relevant declarations of Q0MacroCore.lean. The note also derives a finite bound for repeated primitive words: r consecutive copies of a primitive k-letter word ending at rank P satisfy 16^(k*(r-2)) < P for r>=2. This excludes long repetitions, but leaves arbitrary aperiodic finite paths and the all-parameter length bound open.

The [quantitative matching-block theorem](Q0CommonBlock.md) strengthens aperiodicity: any square of half-length k in a strict-interior signed path obeys `29*k < 64*t+6144` for terminal rank below `16^t`. The more general arbitrary-depth packing theorem bounds matching blocks at positive rank gap. All three new modules compile against the complete exact signed-model dependency closure; `q0_word_constraint` transfers the bound to every position of the forced q0 path via its Source interface. Arbitrary aperiodic itineraries remain unresolved.

### Finite-word realizability

[Q0WordRealization.lean](Q0WordRealization.lean) proves a complementary obstruction to fixed-depth approaches: for **every** nonempty digit word of length k there is a residue u0 < 8*16^(k-1) such that every parameter u=u0+8*16^(k-1)*t follows that word. Consequently every finite word is realizable at arbitrarily large q0 parameters. The proof uses an affine-lifting invariant: after the first digit, the rank coefficient is divisible by 16 and the height coefficient is odd, so each specified next digit admits a lift by one radix-16 digit. All three principal declarations compiled against exact relevant Q0MacroCore declarations in Lean 4.36.0-rc2 with standard axioms. This theorem is about the reduced signed graph; the additional original-root predicates are not asserted to hold for all such words.

In fact the residue is unique: composing a specified word gives 16^k*y_k=(6+24*D)*u+(4+22*D+C), where D is the base-16 digit polynomial and C is the composed offset, even because the first offset is even. The coefficient has 2-adic valuation one, so division by two gives an invertible odd coefficient modulo 8*16^(k-1). The uniqueness argument is presently a paper derivation. This implies at most 4^k parameter cylinders admit a length-k signed path, but all finite words occur. An all-parameter exclusion requires a **size-sensitive** argument relating the least residue of a word to its length, rather than a uniform finite forbidden-word list.

## Size-sensitive rank-window reduction

[Q0RankBarrier.md](Q0RankBarrier.md) and its Lean module prove an exact equivalence between strict-interior k-step past/future crossings at rank a*16^k+b and a small carry strip with initial-cone test. The carry coordinates are O(k) for fixed a,b. The reduction opens a rank-barrier strategy using multiplicatively spaced near-power windows; an all-scale impossibility theorem is still needed. This is not a finite-parameter exclusion or a blank-root decision.

## Next mathematical objective

Prove there cannot be a signed path of length 8u+5 from the entire initial ray, rather than enlarging the finite bound indefinitely. The all-depth secondary F spine is compatible with this goal: arbitrarily many blocks can be forced only at correspondingly large parameter values. A linear or preferably logarithmic termination bound for the signed graph would settle q0. The graph is nondeterministic, so a proof must cover every permitted digit, and must distinguish the strict interior from the invariant boundary rays y=0 and 3y=p.

### Existing residue filters are locally redundant

[Q0LocalFilters.md](Q0LocalFilters.md) proves that the listed depth-16 positive-root residue tests, augmented by the 9/5 exclusion, hold automatically in the second macro of every valid two-macro cone chain. Q0LocalTrace connects the affine formula rows to the actual accelerator. This confines any independent use of these same filters to the oldest boundary; it does not address global rooted ancestry.
