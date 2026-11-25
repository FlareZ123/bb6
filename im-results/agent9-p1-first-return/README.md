# Critical P1 inverse histories: exact first returns and long-cost barriers

**Scope.** Write P=2^n, Q=7P−n−3, and root (14P−2n−16,3). We study the ORIGINAL OddCone relation at total inverse cost m. All statements below concern that critical P1 gate; none claims a machine decision or the global BB(6) upper bound.

**New computational method:** [Exact reverse-block and prefix-only carry](../agent9-p1-reverse-block/README.md) extends the finite experimental range and removes terminal endpoint propagation. See the linked dossier for current evidence and remaining exceptions.

## Main theorems and status

| Original-source consequence | Lean file | Exact-source CI |
|---|---|---|
| n≥14: existence of a right-five history iff a guarded first return of r_j=2r_(j−1) mod(q+j), r_0=1, q+k=Q, with k=m+1 | [SourceFirstReturn.lean](SourceFirstReturn.lean) | [45508108201](https://github.com/FlareZ123/bb6/actions/runs/45508108201) |
| n≥14: every right-five history satisfies 2^max(0,m−n−1)(m+1)>P, hence m>2n−floor(log₂(2n−1)) | [CostSource.lean](CostSource.lean) | [45508888563](https://github.com/FlareZ123/bb6/actions/runs/45508888563) |
| n≥8000: m>4n+2 | [RenewalSource.lean](RenewalSource.lean) | [45510966467](https://github.com/FlareZ123/bb6/actions/runs/45510966467) |
| For every natural B and n≥criticalThreshold B: m>(B+1)n+2; threshold is computable, no external analytic assumptions | [RenewalUnboundedSource.lean](RenewalUnboundedSource.lean) | [45512527543](https://github.com/FlareZ123/bb6/actions/runs/45512527543) |
| n≥8000: m>4n+2+K(n), K(n)=n−(7541+4(floor(log₂ n)+1)); n=10002 requires m≥42416 | [RenewalPrefixSource.lean](RenewalPrefixSource.lean) | [45513140527](https://github.com/FlareZ123/bb6/actions/runs/45513140527) |

All successful runs use Lean 4.36.0-rc2, original dependency closure and standard-axiom checks. [RenewalCost.md](RenewalCost.md) gives an independent paper derivation and [renewal_check.py](renewal_check.py) exact arithmetic regressions.

## Common-clock reverse screening and delayed-carry acceleration (2026-11-25)

For even n, remove the compulsory first selected bit from the modular carry recurrence. Its start is c=(n+2)/2 at clock q=n+4. Every later signed carry lies in 1≤c≤q−3; a legal edge to z at q+1 satisfies 2z=c or 2z=c+q. Consequently its predecessor, if interior, is uniquely (2z) mod q. A single sweep from all terminal interior states at clock F to earlier clocks computes the exact live sets of *all* starts sharing F. A central root is absent precisely when the existing modular width at K=F−n−3 is zero. For 14≤n and 1≤K≤n this excludes the actual critical blank reset, by Agent50's P1CarryWideSource.

[BatchCarry.lean](BatchCarry.lean) proves the exact word/walk and reverse-set equivalences, including a common-clock sweep collecting surviving central births; [BatchCarrySource.lean](BatchCarrySource.lean) proves the universal original-source theorem critical_reset_no_reach_batch and whole-interval corollary. Original dependency closure and ordinary axioms accepted by [CI 45536490304](https://github.com/FlareZ123/bb6/actions/runs/45536490304), pinned source ddec41cfee5f40139f12b3203e696848b5c75e9c. The finite broadword checker [BatchCarryBit.lean](BatchCarryBit.lean) uses Agent28's proved bit spread and only one-sided containment; [BatchCarryFinite.lean](BatchCarryFinite.lean) proposes a single kernel computation for the entire even interval 10002..15000. The identical arithmetic check passed locally via decide +kernel; original-source [finite CI 45537024325](https://github.com/FlareZ123/bb6/actions/runs/45537024325) passed at 3e5ebb8624866c3ac7e63bccc93b964490db136b. This excludes every even critical index in 10002..15000 at the authentic blank root. This is separate from the large numerical runs below.

### Exact-integer experiments (not kernel-certified numerical intervals)

Build [batch.cpp](batch.cpp) with g++ -O3 -std=c++17. Run batch L R, where the common clock is F=2L+3 and R+4≤F. No heuristic cutoff or floating arithmetic enters the recurrence. Observed full scans:

| Even interval L..R | Reverse endpoint visits | Surviving indices at F |
|---|---:|---|
|1000002..1500000|90573065|none|
|1500002..2250000|136508015|2078306, 2017122|
|2250002..3375000|217480630|2917282, 2779710|
|3375002..5062500|346978927|none|
|5062502..7593750|505970701|none|

A singleton batch at F=2n+3 eliminates n=2017122, leaving precisely three indices not covered by the modular n-horizon screen. For those, [reverse_lag.cpp](reverse_lag.cpp) reuses Agent45's exact delayed target model and low-prefix grouping, but replaces the costly initial and subsequent long-window forward bitset images by reverse forests. For a fixed target bit y_i, every bounded endpoint z has at most one predecessor (2z+y_i) mod C_i; the quotient determines the selected bit, and 2z+y_i≥2C_i invalidates the edge. Merge equal predecessor groups using disjoint sets while preserving terminal endpoint IDs; after rewinding, retain exactly the terminal IDs whose roots lie in the specified start set. This computes an exact forward image without iterating through each large forward population. The known delayed targets for each block are reconstructed from the shared low prefix exactly as in laggroup.cpp; the required Agent45 margin inequality is checked for every bit of every proposed block, even one that later dies. In particular the result is a safe block-end extinction cost, not a claim about its minimal value.

Build reverse_lag.cpp with g++ -O3 -std=c++17. Commands: reverse_lag n (10*n) floor(n/8). Results:

| n | Width at n+1 | Safe empty cost K | Max low-prefix groups | Max gap |
|---:|---:|---:|---:|---:|
|2078306|89472|2338095|1|18|
|2779710|1812344|5559415|4|21|
|2917282|553840|8387183|4|25|

Combined with the already completed [Agent28 range 10002..1000000](../agent28-p1-delayed-carry/RANGE-1000000.md), this gives exact-integer computational evidence for every even critical index through 7593750. The prior finite source proofs and the new batch theorem cover through 15000; the large interval checks and delayed-forest algorithm outputs are **not** yet numerical Lean certificates. No P1 decision or BB(6) upper bound follows. Do not repeat this scan or infer an unbounded theorem from the empirical sparsity.

## Two-boundary and authentic reachability extension

[SmallSeed.lean](SmallSeed.lean), [SmallMany.lean](SmallMany.lean), [SmallComplement.lean](SmallComplement.lean) extend the small-seed analysis to either boundary and to all polynomial-size initial residues, including zero mod-seven phases. [BoundarySource.lean](BoundarySource.lean) connects this to both coordinates of original source histories, and [PracticalSource.lean](PracticalSource.lean) derives explicit first-crossing intervals. These adapters passed exact-source CI [45514702164](https://github.com/FlareZ123/bb6/actions/runs/45514702164); the scalar lemmas and source-interface preflights passed locally. First attempt failed due to one argument order mismatch in an imported source lemma, corrected in ec591510ef3f9d36b27bb980f5057c70b9df5d81.

For fixed h,B,p (B≥2,p≥1) and n above the explicit smallThreshold, every OddCone at m≤hn has

    m>0 ⇒ d>2B n^p+1,
    b/2+6>B n^p.

The authentic source theorem then forces some *blank-reachable* odd-cone ancestor of cost m>hn whenever the critical root is blank-reachable, for n above reachableThreshold h. It does not assume any global bound on inverse costs. The positive even-right and exceptional c=1 exits are both excluded below the short-cost cutoff.

The sharper coefficient certificates in RenewalBounds replace the enormous fallback threshold with a checked bit-length trial, using the universal bound (n+1)^d≤2n^d for n≥2d. In particular smallThreshold 4 64 8 1≤8000. Thus for n≥8000 every history of cost m≤4n has b/2+6>64n and (for m>0) d>128n+1. Together with the right-five barrier and the positive inverse edge bound t+1≤n+2, authentic critical-root reachability forces a reachable ancestor in the finite interval

    3n+K(n) < m ≤ 4n+K(n)+2.

At n=10002 this is 32412≤m≤42415. The stronger theorem applies to the actual even-index critical reset as well.

## Exact source/scalar bridge

Set v=(d−1)/2. For root b0+10=2Q, each inverse history has b+2v+2m+8=2Q. A legal forward gap of length k has p+(Q−m)=2^k v', p+8+m≤Q, v'≥2, v'+4+m+k≤Q. These are the Gap constructors. InverseAt_iff_power_mass gives the source-to-gap direction; conversely t=k−1, c=2v'−3, s=Q−(m+k)−v'−2 reconstruct the original source step including b mod 4, size, and exact mass. The reverse unit path runs from shifted right coordinate v at clock Q−m to 1 at clock Q. For right-five v=2, prepend the initial step 1→2. First return and wrap guards are exact.

## Renewal method

After n+3 steps of a proposed short first return (length k), the clock/residue pair is (7P−k,P+k), near phase 1/7. With M=2^L−1 for a period of doubling modulo odd D, define the finite weighted cycle

    H(p) = Σ_(0≤j<L) 2^(L−j)(2^j p mod D).

The identities H(2p mod D)+2Mp=2H(p) and H(p)≡Lp mod D control the early matched wraps and the next phase numerator. An integer lattice gap controls the late block without assuming its wrap word. See [RenewalCore](RenewalCore.lean), [RenewalShadow](RenewalShadow.lean), [RenewalLate](RenewalLate.lean), [RenewalBlock](RenewalBlock.lean), [RenewalNumeric](RenewalNumeric.lean), [RenewalScales](RenewalScales.lean), [RenewalFourN](RenewalFourN.lean).

For arbitrary block count, start (D,G,L)=(7,1,3), U=D/(7G), M=2^L−1 and advance to (49UM,49G,49LU). The normalized D,M,L factors are 7-units; two binomial seven-adic lifts and a first-order binomial congruence prove that D' divides 2^L'−1. No prime factorization or multiplicative-order calculation is needed. A state error coefficient H at degree p updates to A(2C+2), A=2D(H+C), with clock envelope Cn. A sufficient margin is DM A(A(2C+2)+C+8)n^(2p+1)<2^n. The computable threshold is the maximum of the successive coefficient certificates, including the initial-wrap bound. See [RenewalGrid](RenewalGrid.lean), [RenewalBounds](RenewalBounds.lean), [RenewalMany](RenewalMany.lean), [RenewalUnbounded](RenewalUnbounded.lean). D3 has 7348 bits; its next full period is enormous, but its initial shadow extends the explicit 4n barrier by K(n).

For a small seed d and deficit s=q_ref−q with q_ref=7P, the first n steps agree with the static quotient word. Write 2^j d=R+7PU and r_j=R+E, where 0≤E≤sU. If 4(s+8)d<7P and j+2≤s, both margins remain safe. At the block boundary r_n=P(d mod 7)+E. A zero phase continues as a positive polynomial-size seed; a nonzero phase enters the renewal grid. Shifted complement z=q+2−v transports the other boundary: if both positive and the reflected orbit stays ≥2, their sum remains q+j+2, incompatible with an ordinary endpoint of 1. This is the mechanism behind the two-sided theorem.

## Remaining mathematical gap

The exact champion attainment is established elsewhere. The unbounded critical P1 family and BB(6) upper bound remain open. A uniform linear cap on *authentically reachable* odd-cone costs would now exclude every sufficiently large critical index. A pointwise root carry extinction or another contradiction to the first-crossing interval would also suffice. The density-zero result alone cannot settle individual exceptional parameters. Do not extrapolate fixed-block renewal to Θ(P/n) blocks.

The recurrence is the Borwein–Loring recursion a_(t+1)=2(a_t mod t), with a_(q+j+1)=2r_j. Dearden–Metzger, *Running Modulus Recursions* (2010), https://cs.uwaterloo.ca/journals/JIS/VOL13/Dearden/dearden3.pdf. Their general eventual-zero conjecture would not by itself forbid an earlier guarded return. The renewal idea is adapted from Agent50's exact reverse-unit renewal analysis.

## Reproduce

Dispatch `.github/workflows/agent9-p1-shadow-depth.yml` with target `first-return` and the desired source_ref. The workflow compiles the exact transitive source closure and audits exported theorem axioms. No separate workflow is needed.
