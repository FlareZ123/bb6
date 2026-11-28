import Raw36ParentLive12
import Raw36B104
import Raw36B122
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot

/-- The only B1 action still required under D1=1LB after consuming the
    source-accepted 0LB, 0LE and 1RE cylinders. -/
def b1Live1 : List Move := [⟨true,false,4⟩]
def parentLive10 : List PartialMachine := d1Complement.map d1Child ++ b1Live1.map b1Child

theorem b104_identity : b1Child ⟨false,false,4⟩ = BB6.Agent29Raw36B104.b1 := by rfl
theorem b122_identity : b1Child ⟨true,true,4⟩ = BB6.Agent29Raw36B122.b1 := by rfl

theorem b104_cover_at (B : Nat) (hB : 1152 ≤ B) :
    Cover (WeightedBound B) (b1Child ⟨false,false,4⟩) := by
  rw [b104_identity]
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans (BB6.Agent29Raw36B104.bound m hm k d hk hd) hB

theorem b122_cover_at (B : Nat) (hB : 332 ≤ B) :
    Cover (WeightedBound B) (b1Child ⟨true,true,4⟩) := by
  rw [b122_identity]
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans (BB6.Agent29Raw36B122.bound m hm k d hk hd) hB

theorem d1_cover_from_one (B : Nat) (hB : 1152 ≤ B)
    (h : Cover (WeightedBound B) (b1Child ⟨true,false,4⟩)) :
    Cover (WeightedBound B) d1 := by
  apply d1_cover_from_three B (by omega)
  intro mv hm
  simp only [b1Live, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact b104_cover_at B hB
  · exact h
  · exact b122_cover_at B (by omega)

theorem parent_cover_from_ten (B : Nat) (hB : 1152 ≤ B)
    (h : ∀ p ∈ parentLive10, Cover (WeightedBound B) p) :
    Cover (WeightedBound B) parent := by
  apply parent_cover_from_twelve B (by omega)
  intro p hp
  rcases List.mem_append.mp hp with hD | hB1
  · exact h p (List.mem_append_left _ hD)
  · rcases List.mem_map.mp hB1 with ⟨mv,hm,rfl⟩
    simp only [b1Live, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact b104_cover_at B hB
    · exact h _ (List.mem_append_right _ (List.mem_map.mpr ⟨_,by decide,rfl⟩))
    · exact b122_cover_at B (by omega)

theorem b1Live1_count : b1Live1.length = 1 := by decide
theorem parentLive10_count : parentLive10.length = 10 := by decide

#print axioms b104_identity
#print axioms b122_identity
#print axioms b104_cover_at
#print axioms b122_cover_at
#print axioms d1_cover_from_one
#print axioms parent_cover_from_ten
#print axioms b1Live1_count
#print axioms parentLive10_count
end BB6.Agent29Raw36
