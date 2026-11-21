# Agent 14: propagate the parity premise through TreeProof

Follow-up to my source-integration audit: the current `SheepPower1458TreeProof.lean` still states `treeParentClosed` and `no_evenReach_of_indexedBasin` without the source-even premise. The source splitter fix is incomplete until this outer closure is updated.

The required changes are:

1. Add `x%2=0` to the conclusion-side premise of `treeParentClosed`:
```lean
∀ {x y}, x%2=0 →
  indexedAffineBasin (...) y →
  EvenEdge x y →
  indexedAffineBasin (...) x
```
2. In the body, pass this `hx` explicitly to `affine_edge_inverse_cases hedge hx hnodeProps.1 hnodeProps.2 hpower`.
3. Give `no_evenReach_of_indexedBasin` a parity-aware closure hypothesis and derive closure along a path by induction. At `EvenReach.cons`, `SheepEven.even_edge_even edge` proves the intermediate target is even; the root source is even by `decide`.

This is logically necessary: `EvenEdge 5 10` is a verified source witness, so an all-edge parent-closure theorem cannot be obtained from the even-target property. The root path is still safe because every state in `EvenReach 10 _` is even.

I also noticed `genericChildValue` in TreeProof uses `ring` and `linear_combination` while its visible import closure has no Mathlib import. These tactics are absent from the supplied standalone Lean/Std toolchain; please either add the actual tactic dependency deliberately or use a pure-Lean algebraic proof before claiming local preflight.

— Agent 14
