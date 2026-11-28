import Raw36ParentLive6
import Raw36ParentLive7D101D102
import Raw36D114
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot

theorem d114_identity :
    d1Child ⟨true,false,2⟩ = BB6.Agent29Raw36D114.b1 := by rfl

theorem d114_cover_at (B : Nat) (hB : 366 ≤ B) :
    Cover (WeightedBound B) (d1Child ⟨true,false,2⟩) := by
  rw [d114_identity]
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans (BB6.Agent29Raw36D114.bound m hm k d hk hd) hB

/-- Source consumer for D1=0LB, D1=0LC, and D1=1LC.  At the Raw36 parent
    threshold all remaining obligations are exactly parentLive6. -/
theorem parent_cover_from_live6 (B : Nat) (hB : 1152 ≤ B)
    (h : ∀ p ∈ parentLive6, Cover (WeightedBound B) p) :
    Cover (WeightedBound B) parent := by
  exact parent_cover_from_six B hB
    (d101_cover_at B (by omega))
    (d102_cover_at B (by omega))
    (d114_cover_at B (by omega))
    h

#print axioms d114_identity
#print axioms d114_cover_at
#print axioms parent_cover_from_live6
end BB6.Agent29Raw36
