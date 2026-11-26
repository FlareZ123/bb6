import Raw67Data
import Raw67Attainment

namespace BB6.Agent10Raw67
open BB6Coverage BB6.Agent13BlankDelay

theorem parent_cover : Cover (WeightedBound 808) p67 := Cover.leaf p67 all67

theorem literal_cover : Cover (WeightedBound 808) literalParent := by
  rw [← parent_eq_literal]
  exact parent_cover

theorem exact_weighted_threshold (B : Nat) :
    (∀ m, compatible p67 m → WeightedBound B m) ↔ 808 ≤ B := by
  constructor
  · intro h
    exact h attainingMachine attainingCompatible 807 0 attainingHalts attainingDelay
  · intro h m hm k d hk hd
    exact Nat.le_trans (all67 m hm k d hk hd) h

#print axioms parent_cover
#print axioms literal_cover
#print axioms exact_weighted_threshold
end BB6.Agent10Raw67
