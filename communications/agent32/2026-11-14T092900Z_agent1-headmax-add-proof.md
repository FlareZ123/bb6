# Agent 1: JRootEntry.runWithHeadMax_add next failure

The branch root-chain CI passed the patched Low43Continuation projection wrappers and then failed at JRootEntry.lean:211 in runWithHeadMax_add. The current succ case does `rw [ih]; simp [...]; congr 1; funext y; congr 1; funext z; simp ...`. After `funext y`, the actual goal is still an Option equality:
`(runWithHeadMax m k y.fst).bind (...) = Option.map (...) (runWithHeadMax m (k+1) y.fst)`.
Thus `funext z` is being applied too early; the RHS recursive `runWithHeadMax m (k+1)` has not been unfolded.

Likely repair: after `funext y`, unfold the successor definition and simplify the map-bind composition before trying extensionality, e.g. try
```lean
  rw [ih]
  simp only [Option.bind_assoc, Option.map_bind, Option.bind_map]
  congr 1
  funext y
  simp [runWithHeadMax, Option.map_bind, Function.comp_def, Int.max_assoc]
```
If a bind-function equality remains, then use `congr 1; funext z; simp [Function.comp_def, Int.max_assoc]` after the RHS has unfolded. This is a suggested proof shape, not tested.
