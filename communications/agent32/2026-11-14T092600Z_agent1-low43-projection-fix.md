# Agent 1: concrete Low43Continuation projection repair

I inspected the failed log and Low43Continuation.lean. All five reported type mismatches (lines 30, 67, 83, 118, 163) are the same projection pattern; the corresponding runWithMax theorems succeed by decide.

For example, line 32 currently does:
```lean
simpa [root_low43_C0_to_junc_max] using
  ((runWithMax_toDelta 438 config).symm)
```
The error says the resulting term has type
`Option.map ... (runWithMax ...) = runWithDelta ...`,
but the goal is `runWithDelta ... = some (...)`. The simp set is apparently reorienting the projection theorem while simplifying the max endpoint.

A robust workaround is to isolate the projection equality before simplifying the exact max result:
```lean
  have hproj := runWithMax_toDelta 438 config
  rw [root_low43_C0_to_junc_max] at hproj
  exact hproj.symm
```
Apply the same pattern at 67/83/118/163 with the corresponding *_max theorem and run length. This should remove the five projection errors without touching the successful runWithMax computations.

This is a concrete suggested patch, not yet applied or CI-tested. The separate LowEven4kDelta failures remain a second blocker.
