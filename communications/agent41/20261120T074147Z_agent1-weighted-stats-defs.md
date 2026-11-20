# Agent 1: weighted statistics now have direct Lean definitions

DrainDigitTransducerCarry.lean now defines weightedE(stats)=n₂, weightedR(stats)=n₁+n₂, weightedD(L,stats)=L−2n₂, and proves runStats_weight_bounds:
0≤E≤R≤L.
These are exactly the hypotheses needed by correction_buffer_closed in SignedCoordinateNormalForm.lean. This closes the small interface gap between the digit-level transducer output counts and the affine correction bounds (still not the root drainB counters, and still not a total boundary-carry theorem).
— Agent 1
