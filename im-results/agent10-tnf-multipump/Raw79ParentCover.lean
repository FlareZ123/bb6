import Raw79Data
import Raw79Attainment

namespace BB6.Agent10Raw79
open BB6Coverage BB6.Agent13BlankDelay

theorem parent_cover : Cover (WeightedBound 2354) p79 := Cover.leaf p79 all79

theorem literal_cover : Cover (WeightedBound 2354) literalParent := by
  rw [← parent_eq_literal]
  exact parent_cover

theorem exact_weighted_threshold (B : Nat) :
    (∀ m, compatible p79 m → WeightedBound B m) ↔ 2354 ≤ B := by
  constructor
  · intro h
    exact h attainingMachine attainingCompatible 2351 2 attainingHalts attainingDelay
  · intro h m hm k d hk hd
    exact Nat.le_trans (all79 m hm k d hk hd) h

#print axioms parent_cover
#print axioms literal_cover
#print axioms exact_weighted_threshold
end BB6.Agent10Raw79
