# Root residue-seven successor

This directory isolates the genuine-root successor at (m=0, n=16r+7), and separates the source q4 reset prefix from the all-positive counted drain.

## Source reset prefix

**File:** `M0OddResidueSeven.lean`

The theorem `m0Odd_residue7_q4_reset_prefix_source` proves, for every
[
4\le L,\qquad 16r+7<2^L,\qquad 0<a,
]
and arbitrary (b,h), the exact original-(tm2) source run
[
S1(L,16r+7,0,a,0,b,h)
\xrightarrow{\;63+12a+3b\;}
S1(L,16r+6,2,a+b+1,2^b-1,0,h+5+3b).
]

The proof lifts the fixed (m=0,n=5) q4 source prefix through a tape frame. It establishes the exact binary left-facing prefix, preserves the far tail, and composes the generalized q4 suffix. It imports no counted-drain module.

## Counted-drain completion

**File:** `M0OddResidueSevenCounted.lean`

The theorem `m0Odd_residue7_counted_increment_source` composes the reset prefix with the generic S1 all-ones counted drain, yielding
[
S1(L,16r+6,2,a+b+1,0,2^b-1,h+5+3b).
]
This is deliberately separate because its axiom profile depends on the shared S1 counted-drain / carry-output chain. It is not certified until its own transitive `sorryAx` gate passes.

## Blank-root compositions

- `TM63RootResidueSevenPrefix.lean` composes the first eight genuine blank-root middle rows with the reset prefix and stops before the counted drain.
- `TM63RootResidueSeven.lean` composes the same blank-root itinerary with the full counted increment and reaches the next (m=2,n=16r+6) family. This depends on the counted-drain completion.

## Evidence status

The source proof and its root composition are intermediate research results, not a BB(6) solution or an upper bound. The manual original-source workflow is being updated to compile the reset-prefix module before unrelated downstream blockers, then audit the counted-drain module and root compositions separately. Treat a theorem as certified only after the corresponding compile and transitive axiom gate has actually completed.
