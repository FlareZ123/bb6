import Raw36ParentComplement
import Raw36B101
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot

/-- The literal 0LB child is exactly the independently checked B101 table. -/
theorem b101_identity : b1Child ⟨false,false,1⟩ = BB6.Agent29Raw36B101.b1 := by rfl

def b1Live : List Move := [⟨false,false,4⟩,⟨true,false,4⟩,⟨true,true,4⟩]
def parentLive12 : List PartialMachine := d1Complement.map d1Child ++ b1Live.map b1Child

theorem b1Live_count : b1Live.length = 3 := by decide
theorem parentLive12_count : parentLive12.length = 12 := by decide

theorem b101_cover_at (B : Nat) (hB : 315 ≤ B) :
    Cover (WeightedBound B) (b1Child ⟨false,false,1⟩) := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans (BB6.Agent29Raw36B101.bound m hm k d hk hd) hB

theorem d1_cover_from_three (B : Nat) (hB : 1022 ≤ B)
    (h : ∀ mv ∈ b1Live, Cover (WeightedBound B) (b1Child mv)) :
    Cover (WeightedBound B) d1 := by
  apply d1_cover_from_four B hB
  intro mv hm
  simp only [b1Complement, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact b101_cover_at B (by omega)
  · exact h _ (by decide)
  · exact h _ (by decide)
  · exact h _ (by decide)

theorem parent_cover_from_twelve (B : Nat) (hB : 1022 ≤ B)
    (h : ∀ p ∈ parentLive12, Cover (WeightedBound B) p) :
    Cover (WeightedBound B) parent := by
  apply parent_cover_from_thirteen B hB
  intro p hp
  rcases List.mem_append.mp hp with hD | hB1
  · exact h p (List.mem_append_left _ hD)
  · rcases List.mem_map.mp hB1 with ⟨mv,hm,rfl⟩
    simp only [b1Complement, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact b101_cover_at B (by omega)
    · exact h _ (List.mem_append_right _ (List.mem_map.mpr ⟨_,by decide,rfl⟩))
    · exact h _ (List.mem_append_right _ (List.mem_map.mpr ⟨_,by decide,rfl⟩))
    · exact h _ (List.mem_append_right _ (List.mem_map.mpr ⟨_,by decide,rfl⟩))

#print axioms b101_identity
#print axioms b1Live_count
#print axioms parentLive12_count
#print axioms b101_cover_at
#print axioms d1_cover_from_three
#print axioms parent_cover_from_twelve
end BB6.Agent29Raw36
