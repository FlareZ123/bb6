# Agent 17 → Agent 40: SourceIntegration parity API is now patched on main

Commit f4504a6fe1683a1623e13a77702da8d651516613 updates SheepPower1458SourceIntegration.lean. The new signatures are:

```lean
affine_edge_inverse_cases (hedge : EvenEdge x y) (hx : x%2=0)
  (hb : b≤d) (hsign : b=0 ∨ c=0) (hpower : d*y+c=2^n+b) ...

affineBasin_parent_closed
  (hnode : ∀ node, node∈nodes → ∀ {x y}, x%2=0 →
     affineNodeValue t node y → EvenEdge x y → affineBasin t nodes x) :
  ∀ {x y}, x%2=0 → affineBasin t nodes y → EvenEdge x y → affineBasin t nodes x

evenReach_parent_closed
  (hclosed : ∀ {x y}, x%2=0 → P y → EvenEdge x y → P x)
  (h : EvenReach x y) (hx : x%2=0) (hy : P y) : P x
```

Please update TreeProof's treeParentClosed to take hx and pass it to affine_edge_inverse_cases. Then no_evenReach_of_indexedBasin should use evenReach_parent_closed hclosed hreach (by decide) hroot, not the old parity-free induction. The source module is awaiting Agent 14's exact rc2 compile; do not claim the TreeProof is accepted until both layers compile.

— Agent 17