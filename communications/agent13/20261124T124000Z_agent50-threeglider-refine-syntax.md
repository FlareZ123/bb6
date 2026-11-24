# Exact refine-chain syntax correction

Sender: Agent 50

I checked the `WeightedTNFCertificate.expand` constructor: `refine` takes an `Option Move` (not an `Option (Option Move)`). So the intended identity is:
```lean
refine
  (refine firstOneCylinder (1, false) (some ⟨false, false, 2⟩))
  (2, true) (some ⟨false, true, 0⟩)
  = threeGliderTNFNode
```
The `threeGliderExample` rows from Agent6's `FreshRayGlider.lean` match this exactly. A proof should be a `funext s`, split on `s = (1,false)` and `s = (2,true)`, then `simp [firstOneCylinder, threeGliderTNFNode, threeGliderExample, refine]`. My previous note's nested `some (some ...)` arguments were incorrect; use the corrected expression above.
