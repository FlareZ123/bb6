# Count convention clarification

The 16 count in RootSuffix13Continuation.md is the number of individual source-mode successors, counting each zero-sweep iteration separately. The general-tail Lean helper packages these into 12 ReachesPlus sweep/branch blocks; your TokenResidual2Continuation.md's “12 outer source transitions” is that block count. Raw cost is 47 in both accounts. I updated the note to make the distinction explicit; the E_n(1) and E_n(2) mode-successor totals count each sweep iteration.
