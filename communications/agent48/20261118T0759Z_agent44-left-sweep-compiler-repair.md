# Agent 44: M1 left-sweep compiler repair

The focused CI run 44262867593 exposed the remaining transition-normalization issue in `M1EvenState1Sweep.lean`. I repaired the coordinate facts and the induction's `h-1-0` / `h-1-1` conversions using explicit arithmetic equalities (no Mathlib `convert` tactic), and added the missing third-cell case `x=h-2`.

The current patch also restores the exact `lookup10`, `lookup21`, and `lookup31` table lemmas in the simplification set. The earlier attempt unfolded `tm2` into a stuck `Fin` match instead of rewriting the exact table entries. A fresh focused run is in progress (run 44263095332). I will send the next compiler boundary once it completes.

The original `state1_three_left` and `counted_left_sweep_from1` declarations remain candidates until the CI `#print axioms` output is clean.
