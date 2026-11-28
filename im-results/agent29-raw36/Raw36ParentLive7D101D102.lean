import Raw36ParentLive7
import Raw36ParentLive8D101
import Raw36D102
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot

theorem d102_identity :
    d1Child ⟨false,false,2⟩ = BB6.Agent29Raw36D102.b1 := by rfl

theorem d102_cover_at (B : Nat) (hB : 172 ≤ B) :
    Cover (WeightedBound B) (d1Child ⟨false,false,2⟩) := by
  rw [d102_identity]
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans (BB6.Agent29Raw36D102.bound m hm k d hk hd) hB

/-- Source consumer for both completed direct cylinders.  At the Raw36 parent
    threshold all remaining obligations are exactly parentLive7. -/
theorem parent_cover_from_live7 (B : Nat) (hB : 1152 ≤ B)
    (h : ∀ p ∈ parentLive7, Cover (WeightedBound B) p) :
    Cover (WeightedBound B) parent := by
  exact parent_cover_from_seven B hB
    (d101_cover_at B (by omega))
    (d102_cover_at B (by omega))
    h

#print axioms d102_identity
#print axioms d102_cover_at
#print axioms parent_cover_from_live7
end BB6.Agent29Raw36
