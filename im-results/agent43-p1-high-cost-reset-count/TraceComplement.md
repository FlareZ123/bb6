# Full delayed-carry complement and large-index experiments (2026-11-26)

## Exact Lean results

For the actual `BB6.Agent45.DelayedCarry.Trace`, define
`cap n i = n+i+1-(if n<i then 1 else 0)`. At any trace length i>=1,
the selected word B is odd, B<2^i, and the carry a<=cap n i.
For positive even n the reflection

    (B,a) -> (2^i-B, cap n i-a)

preserves every trace, fixes the initial state, and replaces every selected
bit after the compulsory first one by its complement. This is not limited
to the zero-target modular window. The reflected delayed target pair sums
to 0 for i<n, 2 for i=n, and 1 for i>n, giving the exact carry identity
`2*cap n (i+1)+target n i B+target n i (2^i-B)=cap n i+n+i+3`.
At i>=2 every pair has one B=1 mod 4 and one B=3 mod 4.

[TraceComplement.lean](TraceComplement.lean) proves all these statements.
[TraceComplementCover.lean](TraceComplementCover.lean) proves that extension
commutes with reflection, `HalfCovered` lifts to ordinary `Covered` by
adding reflected pairs, any sound block checker preserves the canonical
half, and an empty half-cover gives the original full extinction theorem.

Local Lean 4.36.0-rc2 checked both modules against the exact repository
LagCore (11a318851f288c99f04cc63fb83af3012166bc91), BitCarry
(17fa7bcd8a09f801fc87e5c395c4fc15b8fe32de), and LagChecker
(dc5bb163011b6985cdb5ce46d67c1b3d91fda5a5). No source changes to those
dependencies. All exported theorem audits have only ordinary Lean axioms.
No new workflow was started. The existing LongConeSource theorem already
accepts an empty ordinary cover, so this is a direct mathematical bridge
from half-cover extinction to the previous source criterion.

## New numerical result

[packed_prefix.cpp](packed_prefix.cpp) adapts Agent9's exact reverse-block
prefix method: immutable shared packed bit blocks store the low product
bits, run lengths update online, and the first selected bit after the seed
is fixed at zero in half mode. Checkpoints are untrusted restart artifacts.
The local full/half regression at n=3342 gave the same extinction depth
13768 (h=417, K=14000).

New critical index n=155728894, previously a full modular-horizon survivor
in Agent9's scan: build with g++ -O3 -march=native -fopenmp packed_prefix.cpp
-o packed_prefix; run OMP_NUM_THREADS=2 ./packed_prefix 155728894 622915576
77864447 half. The exact arithmetic experiment returned:

    s=1 h=77864447 old=1 mids=16 next=1 work=706024907 filter=32645244 gap=26 sec=34.8202
    s=77864448 h=77864447 old=1 mids=13 next=0 work=875851951 filter=34390202 gap=26 sec=77.26
    END 155728894 233593342

Exit 0, maximum RSS 321064 KiB. The extinction depth is below the existing
margin-free practical cutoff. This is new numerical evidence, not a
kernel-certified numerical exclusion. The remaining certificate obligation
is to transport the actual finite reverse images into the Lean block-cover
interface. The compiled v2 source differs from the current v3 source only
in widened arithmetic/range guard (same result for this index).

The n=123109726 full-mode first attempt at h=15388715 was stopped by its
600s timeout after the stage s=169275866 (next four prefixes). That is
not an exclusion. The new half-mode experiments use h=n/2 and restart
checkpoints; their final outputs will be recorded separately.

Neither this computation nor the new symmetry proves the unbounded P1
index quantifier, a machine decision, or a BB(6) bound.

## Second delayed extinction and wider search

Using the packed implementation with h=n/2, K=4n, OMP_NUM_THREADS=2:

    ./packed_prefix 230417762 921671048 115208881 half
    s=1 next=2
    s=115208882 next=4
    s=230417763 next=1
    s=345626644 next=0
    END 230417762 576044406

Exit 0, wall 431.565 seconds under concurrent computations. The extinction depth is below the existing practical cutoff. This closes a second modular-horizon survivor numerically, with formal numerical coverage still required.

The n=123109726 half-mode run (h=61554863, K=492438904) instead survived: candidate counts 3,1,2,4,2,1. Its four-n horizon is not an extinction result. An extended 6n run is in progress from an untrusted checkpoint at s=307774316; one previous stage was repeated to recover the last surviving prefix.

[packed_wide.cpp](packed_wide.cpp), exact blob ddd2fdcdba145cafccb5c67f37efb008bc0092ef, uses uint32_t clocks/carries, checks n+K+3<UINT32_MAX, and uses uint128_t for the margin product. It permits increasing K at restart after checking the stored maximum gap against the new margin bound. The n=3342 regression again returned END 3342 13768. The n=514893090 full modular survivor is being tested with K=2059572360, h=257446545. All these runs are numerical experiments, not proof certificates.


## Completed deeper and wider delayed extinctions

The 123109726 half-mode continuation used the wide program with K=738658356
(6n), h=61554863, OMP_NUM_THREADS=2, from the prior checkpoint at s=307774316:

    RESUME s=307774316 count=2
    s=307774316 h=61554863 old=2 mids=63 next=1 work=2310256613 filter=95049981 gap=28 sec=64.4893
    s=369329179 h=61554863 old=1 mids=36 next=0 work=1307170642 filter=49824951 gap=28 sec=128.879
    END 123109726 492438905

Exit 0. The extinction is at 4n+1, beyond the practical margin-free cutoff.
The checkpoint is untrusted; this remains numerical evidence, with the
midpoint cover and margin premises requiring certification.

The new full modular survivor n=514893090 was also eliminated numerically.
OMP_NUM_THREADS=1 ./packed_wide 514893090 2059572360 257446545 half new514.chk
from an empty checkpoint:

    s=1 h=257446545 old=1 mids=14 next=1 work=2363814260 filter=100093604 gap=27 sec=130.016
    s=257446546 h=257446545 old=1 mids=17 next=1 work=2908202780 filter=124613683 gap=30 sec=285.246
    s=514893091 h=257446545 old=1 mids=19 next=1 work=3382030009 filter=106497868 gap=30 sec=466.046
    s=772339636 h=257446545 old=1 mids=26 next=0 work=4030738184 filter=126586121 gap=30 sec=672.627
    END 514893090 1287232726

Exit 0, below practical cutoff. All four new extinctions are computational
results, not source-certified numerical exclusions.

## Formal block-margin certificate layer

[HalfBlockMargin.lean](HalfBlockMargin.lean) proves that a canonical half
midpoint cover, containing each viable h-step midpoint extendible for the
remaining n-h steps, plus the new block's margin condition, advances the
half-cover and all accumulated prefix margins simultaneously. The empty
half certificate converts to the existing ordinary LagCert Cert. This
allows the deeper extinction at 4n+1 to use the margin-based route instead
of the practical cutoff, provided its numerical premises are certified.

[RunMargin.lean](RunMargin.lean) proves the mixed-bit-window lower bound
on resMin and reduces all prefix margins of a word to packed AND/OR checks.
[RunMarginFast.lean](RunMarginFast.lean) uses k doubling shift-and-OR or
shift-and-AND operations to check every length-2^k window simultaneously.
The observed maximum run gaps of the four successful runs are <=30, so
32-bit windows suffice for their full words, with short prefixes handled
by oddness. These modules have been checked locally against the actual
original Lean LagCore, LagChecker and LagCert, with ordinary axioms only.
The numerical midpoint coverage remains the outstanding obligation.
