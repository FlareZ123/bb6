import Raw36ParentLive8
import Raw36D101
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot

theorem d101_identity :
    d1Child ⟨false,false,1⟩ = BB6.Agent29Raw36D101.b1 := by rfl

theorem d101_cover_at (B : Nat) (hB : 450 ≤ B) :
    Cover (WeightedBound B) (d1Child ⟨false,false,1⟩) := by
  rw [d101_identity]
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans (BB6.Agent29Raw36D101.bound m hm k d hk hd) hB

/-- Source consumer for the complete D1=0LB cylinder.  At the existing
    Raw36 parent threshold, all remaining obligations are exactly parentLive8. -/
theorem parent_cover_from_live8 (B : Nat) (hB : 1152 ≤ B)
    (h : ∀ p ∈ parentLive8, Cover (WeightedBound B) p) :
    Cover (WeightedBound B) parent := by
  exact parent_cover_from_eight B hB (d101_cover_at B (by omega)) h

#print axioms d101_identity
#print axioms d101_cover_at
#print axioms parent_cover_from_live8
end BB6.Agent29Raw36
