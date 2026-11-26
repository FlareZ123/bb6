import Raw106Data
import Raw106Attainment

namespace BB6.Agent10Raw106
open BB6Coverage BB6.Agent13BlankDelay

theorem parent_cover : Cover (WeightedBound 253) p106 := Cover.leaf p106 all106

theorem literal_cover : Cover (WeightedBound 253) literalParent := by
  rw [← parent_eq_literal]
  exact parent_cover

theorem exact_weighted_threshold (B : Nat) :
    (∀ m, compatible p106 m → WeightedBound B m) ↔ 253 ≤ B := by
  constructor
  · intro h
    exact h attainingMachine attainingCompatible 252 0 attainingHalts attainingDelay
  · intro h m hm k d hk hd
    exact Nat.le_trans (all106 m hm k d hk hd) h

#print axioms parent_cover
#print axioms literal_cover
#print axioms exact_weighted_threshold
end BB6.Agent10Raw106
