import Raw36D1Complement
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot

abbrev d1Child (mv : Move) : PartialMachine := refine parent (3,true) (some mv)

def d1Complement : List Move := [⟨false,false,0⟩,⟨true,false,0⟩,⟨false,false,1⟩,⟨false,false,2⟩,⟨true,false,2⟩,⟨false,false,4⟩,⟨false,true,4⟩,⟨true,false,4⟩,⟨true,true,4⟩]
def parentComplement : List PartialMachine := d1Complement.map d1Child ++ b1Complement.map b1Child

theorem parentComplement_count : parentComplement.length = 13 := by decide

theorem remaining_explicit : remaining = [
  ([⟨false,false,0⟩], d1Child ⟨false,false,0⟩),
  ([⟨true,false,0⟩], d1Child ⟨true,false,0⟩),
  ([⟨false,false,1⟩], d1Child ⟨false,false,1⟩),
  ([⟨true,false,1⟩,⟨false,false,0⟩], b1Child ⟨false,false,0⟩),
  ([⟨true,false,1⟩,⟨false,true,0⟩], b1Child ⟨false,true,0⟩),
  ([⟨true,false,1⟩,⟨true,false,0⟩], b1Child ⟨true,false,0⟩),
  ([⟨true,false,1⟩,⟨true,true,0⟩], b1Child ⟨true,true,0⟩),
  ([⟨true,false,1⟩,⟨false,false,1⟩], b1Child ⟨false,false,1⟩),
  ([⟨true,false,1⟩,⟨false,true,1⟩], b1Child ⟨false,true,1⟩),
  ([⟨true,false,1⟩,⟨true,false,1⟩], b1Child ⟨true,false,1⟩),
  ([⟨true,false,1⟩,⟨false,true,2⟩], b1Child ⟨false,true,2⟩),
  ([⟨true,false,1⟩,⟨true,false,2⟩], b1Child ⟨true,false,2⟩),
  ([⟨true,false,1⟩,⟨true,true,2⟩], b1Child ⟨true,true,2⟩),
  ([⟨true,false,1⟩,⟨false,true,3⟩], b1Child ⟨false,true,3⟩),
  ([⟨true,false,1⟩,⟨false,false,4⟩], b1Child ⟨false,false,4⟩),
  ([⟨true,false,1⟩,⟨false,true,4⟩], b1Child ⟨false,true,4⟩),
  ([⟨true,false,1⟩,⟨true,false,4⟩], b1Child ⟨true,false,4⟩),
  ([⟨true,false,1⟩,⟨true,true,4⟩], b1Child ⟨true,true,4⟩),
  ([⟨false,false,2⟩], d1Child ⟨false,false,2⟩),
  ([⟨true,false,2⟩], d1Child ⟨true,false,2⟩),
  ([⟨false,false,4⟩], d1Child ⟨false,false,4⟩),
  ([⟨false,true,4⟩], d1Child ⟨false,true,4⟩),
  ([⟨true,false,4⟩], d1Child ⟨true,false,4⟩),
  ([⟨true,true,4⟩], d1Child ⟨true,true,4⟩)] := by rfl

theorem parent_cover_from_thirteen (B : Nat) (hB : 1022 ≤ B)
    (h : ∀ p ∈ parentComplement, Cover (WeightedBound B) p) :
    Cover (WeightedBound B) parent := by
  have hd1 : Cover (WeightedBound B) d1 := d1_cover_from_four B hB (by
    intro mv hm
    exact h _ (List.mem_append_right _ (List.mem_map.mpr ⟨mv,hm,rfl⟩)))
  have hd1kid (mv : Move) : Cover (WeightedBound B) (b1Child mv) := by
    apply Cover.leaf
    intro m hm
    exact hd1.sound m ((compatible_refine_iff d1 m (1,true) (by decide) _).mp hm).1
  apply cover (by omega)
  intro e he
  rw [remaining_explicit] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h _ (List.mem_append_left _ (List.mem_map.mpr ⟨⟨false,false,0⟩,by decide,rfl⟩))
  · exact h _ (List.mem_append_left _ (List.mem_map.mpr ⟨⟨true,false,0⟩,by decide,rfl⟩))
  · exact h _ (List.mem_append_left _ (List.mem_map.mpr ⟨⟨false,false,1⟩,by decide,rfl⟩))
  · exact hd1kid _
  · exact hd1kid _
  · exact hd1kid _
  · exact hd1kid _
  · exact hd1kid _
  · exact hd1kid _
  · exact hd1kid _
  · exact hd1kid _
  · exact hd1kid _
  · exact hd1kid _
  · exact hd1kid _
  · exact hd1kid _
  · exact hd1kid _
  · exact hd1kid _
  · exact hd1kid _
  · exact h _ (List.mem_append_left _ (List.mem_map.mpr ⟨⟨false,false,2⟩,by decide,rfl⟩))
  · exact h _ (List.mem_append_left _ (List.mem_map.mpr ⟨⟨true,false,2⟩,by decide,rfl⟩))
  · exact h _ (List.mem_append_left _ (List.mem_map.mpr ⟨⟨false,false,4⟩,by decide,rfl⟩))
  · exact h _ (List.mem_append_left _ (List.mem_map.mpr ⟨⟨false,true,4⟩,by decide,rfl⟩))
  · exact h _ (List.mem_append_left _ (List.mem_map.mpr ⟨⟨true,false,4⟩,by decide,rfl⟩))
  · exact h _ (List.mem_append_left _ (List.mem_map.mpr ⟨⟨true,true,4⟩,by decide,rfl⟩))

#print axioms remaining_explicit
#print axioms parentComplement_count
#print axioms parent_cover_from_thirteen
end BB6.Agent29Raw36
