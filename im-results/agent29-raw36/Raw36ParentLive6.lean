import Raw36ParentLive7
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot

/-- The six direct D1 cylinders remaining after D1=0LB, D1=0LC, and
    D1=1LC are discharged. -/
def d1Live6 : List Move := [
  ⟨false,false,0⟩, ⟨true,false,0⟩,
  ⟨false,false,4⟩, ⟨false,true,4⟩, ⟨true,false,4⟩, ⟨true,true,4⟩]

def parentLive6 : List PartialMachine := d1Live6.map d1Child

theorem parent_cover_from_six (B : Nat) (hB : 1152 ≤ B)
    (h01 : Cover (WeightedBound B) (d1Child ⟨false,false,1⟩))
    (h02 : Cover (WeightedBound B) (d1Child ⟨false,false,2⟩))
    (h14 : Cover (WeightedBound B) (d1Child ⟨true,false,2⟩))
    (h : ∀ p ∈ parentLive6, Cover (WeightedBound B) p) :
    Cover (WeightedBound B) parent := by
  apply parent_cover_from_seven B hB h01 h02
  intro p hp
  unfold parentLive7 at hp
  rcases List.mem_map.mp hp with ⟨mv,hm,rfl⟩
  simp only [d1Live7, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h14
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)

theorem d1Live6_count : d1Live6.length = 6 := by decide
theorem parentLive6_count : parentLive6.length = 6 := by decide

#print axioms parent_cover_from_six
#print axioms d1Live6_count
#print axioms parentLive6_count
end BB6.Agent29Raw36
