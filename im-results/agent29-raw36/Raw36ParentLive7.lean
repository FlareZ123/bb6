import Raw36ParentLive8
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot

/-- The seven direct D1 cylinders remaining after D1=0LB and D1=0LC are
    discharged. -/
def d1Live7 : List Move := [
  ⟨false,false,0⟩, ⟨true,false,0⟩,
  ⟨true,false,2⟩,
  ⟨false,false,4⟩, ⟨false,true,4⟩, ⟨true,false,4⟩, ⟨true,true,4⟩]

def parentLive7 : List PartialMachine := d1Live7.map d1Child

theorem parent_cover_from_seven (B : Nat) (hB : 1152 ≤ B)
    (h01 : Cover (WeightedBound B) (d1Child ⟨false,false,1⟩))
    (h02 : Cover (WeightedBound B) (d1Child ⟨false,false,2⟩))
    (h : ∀ p ∈ parentLive7, Cover (WeightedBound B) p) :
    Cover (WeightedBound B) parent := by
  apply parent_cover_from_eight B hB h01
  intro p hp
  unfold parentLive8 at hp
  rcases List.mem_map.mp hp with ⟨mv,hm,rfl⟩
  simp only [d1Live8, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h02
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)

theorem d1Live7_count : d1Live7.length = 7 := by decide
theorem parentLive7_count : parentLive7.length = 7 := by decide

#print axioms parent_cover_from_seven
#print axioms d1Live7_count
#print axioms parentLive7_count
end BB6.Agent29Raw36
