import Raw36ParentLive7D102D114
import Raw36D101

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Consume the complete direct Raw36 D1=0LB parent after the already accepted
D1=0LC and D1=1LC reductions.  The remaining six direct D1 cylinders stay
explicit Cover assumptions.
-/

namespace BB6.Agent18Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent29Raw36

def d1LiveAfter01_02_14 : List Move := [
  ⟨false,false,0⟩, ⟨true,false,0⟩,
  ⟨false,false,4⟩, ⟨false,true,4⟩, ⟨true,false,4⟩, ⟨true,true,4⟩]

def parentLiveAfter01_02_14 : List PartialMachine :=
  d1LiveAfter01_02_14.map d1Child

theorem d101_same_source :
    d1Child ⟨false,false,1⟩ = BB6.Agent29Raw36D101.b1 := by rfl

theorem d101_cover_at (B : Nat) (hB : 450 ≤ B) :
    Cover (WeightedBound B) (d1Child ⟨false,false,1⟩) := by
  rw [d101_same_source]
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans (BB6.Agent29Raw36D101.bound m hm k d hk hd) hB

theorem parent_cover_from_live6_after01_02_14 (B : Nat) (hB : 1152 ≤ B)
    (h : ∀ p ∈ parentLiveAfter01_02_14, Cover (WeightedBound B) p) :
    Cover (WeightedBound B) parent := by
  apply parent_cover_from_live7_after02And14 B hB
  intro p hp
  unfold parentLiveAfter02And14 at hp
  rcases List.mem_map.mp hp with ⟨mv,hm,rfl⟩
  simp only [d1LiveAfter02And14, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact d101_cover_at B (by omega)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)

theorem after01_02_14_count :
    parentLiveAfter01_02_14.length = 6 := by decide

#print axioms d101_same_source
#print axioms d101_cover_at
#print axioms parent_cover_from_live6_after01_02_14
#print axioms after01_02_14_count
end BB6.Agent18Raw36
