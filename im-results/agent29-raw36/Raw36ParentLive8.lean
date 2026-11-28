import Raw36ParentLive9
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot

/-- The eight direct D1 cylinders remaining after the D1=0LB cylinder is
    discharged.  This is the exact Raw36 live roster consumed by
    `parent_cover_from_eight`. -/
def d1Live8 : List Move := [
  ⟨false,false,0⟩, ⟨true,false,0⟩,
  ⟨false,false,2⟩, ⟨true,false,2⟩,
  ⟨false,false,4⟩, ⟨false,true,4⟩, ⟨true,false,4⟩, ⟨true,true,4⟩]

def parentLive8 : List PartialMachine := d1Live8.map d1Child

/-- Consuming the direct D1=0LB cylinder from the accepted nine-live Raw36
    reduction leaves exactly eight concrete direct D1 obligations. -/
theorem parent_cover_from_eight (B : Nat) (hB : 1152 ≤ B)
    (h01 : Cover (WeightedBound B) (d1Child ⟨false,false,1⟩))
    (h : ∀ p ∈ parentLive8, Cover (WeightedBound B) p) :
    Cover (WeightedBound B) parent := by
  apply parent_cover_from_nine B hB
  intro p hp
  unfold parentLive9 at hp
  rcases List.mem_map.mp hp with ⟨mv,hm,rfl⟩
  simp only [d1Complement, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h01
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)

theorem d1Live8_count : d1Live8.length = 8 := by decide
theorem parentLive8_count : parentLive8.length = 8 := by decide

#print axioms parent_cover_from_eight
#print axioms d1Live8_count
#print axioms parentLive8_count
end BB6.Agent29Raw36
