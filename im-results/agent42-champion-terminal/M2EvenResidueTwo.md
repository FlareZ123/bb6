# Marker-2 even residue-two source row (m=2, n=8k+2)

**Status (15 November 2026):** the universal original-TM2 proof script is now written in Lean, but the current source and its counted/root consumers have **not** passed a current-source Lean 4.36.0-rc2 compile or transitive axiom audit. This remains intermediate work in im-results, not a certified champion extension.

## Exact source contract

The row theorem in M2EvenResidueTwo.lean proves the q4 prefix and full reset-prefix source runs for every L, k, a, b satisfying the displayed width and positivity hypotheses:

- m2Even_residue2_q4_prefix_source: cost 44+12a, reaching the q4 configuration with left-facing target q4LeftFacing L (8k+1) a and the required right-facing q4 shape.
- m2Even_residue2_q4_reset_prefix_source: cost resetPrefixCost 2 (8k+2) a b = 83+12a+3b, reaching the S1 configuration with marker 1 and index 8k+1.
- M2EvenResidueTwoCounted.lean adds m2Even_residue2_counted_increment_source by composing that reset prefix with the generic counted S1 drain. Its final state is
  s1Config L (8k+1) 1 (a+b+2) 0 (2^b-1) (h+5+3*b),
  at total cost proposedIncrementCost 2 (8k+2) a b
  = 6*4^b + 42*2^b - 9*b + 35 + 12*a.

These are Lean proof terms in the repository source, not yet kernel-checked at the current revision. The #print axioms commands are present in the source, but their output has not yet been obtained for this revision.

The counted adapter has a separate unresolved dependency: S1CountedDrain.lean and its generic carry-prefix/H-run closure have not passed a full original-import compile and transitive axiom audit. Agent 48's README lists CountedCarryPrefixHRun.lean, S1CarryInc0.lean, S1CountedInc0.lean, and S1CountedDrain.lean as an open source-validation obligation. Thus a successful compile of this row module alone would not validate the counted increment.

## Binary boundary and reusable finite bridge

The proof establishes the exact head-facing binary decompositions

- binDec L (8k+2) = d1 ++ d0 ++ d1 ++ binDec (L-3) k;
- binDec L (8k+1) = d0 ++ d1 ++ d1 ++ binDec (L-3) k.

The source and target S1/q4 left-facing streams therefore share the exact tail
[true] ++ d1 ++ binDec (L-3) k ++ lh
after their first 3a+12 cells. The finite prefixes are defined explicitly in M2EvenResidueTwo.lean and have equal length 3a+12.

The local kernel is the existing 38-step n=6 bridge from M2EvenSixQ4Prefix.lean:

- input: state 3, head 0, ones at [-7,-6,-5,-4,-1,2];
- output: state 4, head 2, ones at [1,-1,-4,-7,-8,-9,2].

The new row does not claim that the entire source tape equals the n=6 base tape. It proves equality only on the framed region read by the bridge, then preserves the untouched common tail. A (3a+2)-cell left sweep, the 38-step bridge, and a 3a-step E scan give the 44+12a prefix. The head-bound argument confines every intermediate head to the framed half-line beginning at h-(3a+11). The q4 suffix then contributes 39+3b steps.

The counted drain adds 6*4^b + 42*2^b - 12*b - 48 steps. Adding the reset prefix and drain yields the total formula above and the stated endpoint. The deterministic replay in m2_even_residue2_replay.js reports 120/120 exact finite endpoint matches over its tested parameter grid; this is computational evidence, not a substitute for the quantified Lean proof.

## Authentic-root composition

Agent 48's source-only candidate wrappers in im-results/agent48-counted-inc0/ compose the row as follows:

1. Middle 20: m=1, n=16r-4 = 8(2r-1)+4, using Agent 41's m=1 even residue-four increment; output m=0, n=16r-5.
2. Middle 21: the generic all-odd m=0 increment at n=16r-5; output m=2, n=16r-6.
3. Middle 22: m=2, n=16r-6 = 8(2r-1)+2, using this marker-2 residue-two counted increment with quotient k=2r-1; output m=1, n=16r-7.

The exact root endpoint/counter/head recurrences are defined in TM63RootMiddle20.lean, TM63RootMiddle21.lean, and TM63RootMiddle22.lean. All three wrappers, the counted adapter, and their complete imported source closure remain uncompiled candidates. The quotient identity is exact arithmetic; it does not itself validate the underlying source-run theorems.

## Validation gate and next action

The manual-only workflow .github/workflows/agent42-m2-even-residue-two.yml compiles the M2EvenResidueTwo.lean prefix/reset-prefix module and its listed dependencies, with a sorryAx gate. It does **not** compile M2EvenResidueTwoCounted.lean or the middle-20/21/22 root wrappers. No run of this workflow has been dispatched for the current source.

The next action is a local Lean 4.36.0-rc2 compile of the smallest dependency closure for M2EvenResidueTwo.lean, followed by inspection of the printed axiom sets for both exported source theorems. After that, separately close the generic S1CountedDrain dependency gate (including the H-run/carry-prefix modules), then compile M2EvenResidueTwoCounted.lean and the TM63RootMiddle22 dependency chain. The existing row workflow can then be used once as an acceptance check; it does not certify the counted adapter or root wrappers. Do not describe this row or the middle-22 wrapper as a verified blank-root lower-bound extension until those checks pass.

This row is distinct from the earlier fixed-base m=2,n=4 Q4 candidate and from the m=2,n=8k+6 residue-six row. It is an intermediate source theorem only: it does not complete the TM63 halt itinerary, establish an exact champion score, or address the universal BB(6) upper bound.
