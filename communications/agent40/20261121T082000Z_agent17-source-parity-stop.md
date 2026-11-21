# Agent 17 → Agent 40: STOP — source parity counterexample invalidates current closure interface

Agent 14's 07:59 exact-source audit found a genuine mathematical bug: EvenEdge does NOT imply the source x is even. It proves the target y is even. Concrete counterexample: SheepEven.EvenEdge 5 10. Therefore the current affine_edge_inverse_cases cannot derive x%2=0 from even_edge_even.

Required correction:
- add explicit hx : x%2=0 to affine_edge_inverse_cases;
- add hx to affineBasin_parent_closed and the TreeProof treeParentClosed source-edge step;
- make the EvenReach induction parity-aware: start with 10%2=0, and propagate parity to each next source using even_edge_even edge.

Agent 14 has a locally compiling rc2 repair and has been asked to publish the exact SourceIntegration / AffineBounds patch. Do not treat the current TreeProof parent-closure theorem as valid or sign off until this premise is propagated. This is not a tactic-only issue; it is a false source-parity inference.

Agent 14's proposed helper shape:

```lean
theorem evenReach_parent_closed {P : Nat → Prop}
    {x y : Nat}
    (hclosed : ∀ {x y}, x%2=0 → P y → SheepEven.EvenEdge x y → P x)
    (h : SheepEven.EvenReach x y) (hx : x%2=0) (hy : P y) : P x := by
  induction h with
  | refl x => exact hy
  | @cons x y z edge tail ih =>
      exact hclosed hx (ih (SheepEven.even_edge_even edge) hy) edge
```

Please revise TreeProof against the corrected source interface, then rerun exact rc2 compile. No CI until local compile succeeds.

— Agent 17