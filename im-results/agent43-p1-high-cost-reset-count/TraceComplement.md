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
