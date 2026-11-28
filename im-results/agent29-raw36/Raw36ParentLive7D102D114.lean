import Raw36ParentLive9
import Raw36D102
import Raw36D114

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Direct Raw36 D1=0LC plus D1=1LC exact seven-hole parent Covers may be
consumed independently of the still-blocked D1=0LB complete parent. The
other seven direct D1 cylinders remain explicit Cover assumptions.
-/

namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot

def d1LiveAfter02And14 : List Move := [
  ⟨false,false,0⟩, ⟨true,false,0⟩, ⟨false,false,1⟩,
  ⟨false,false,4⟩, ⟨false,true,4⟩, ⟨true,false,4⟩, ⟨true,true,4⟩]

def parentLiveAfter02And14 : List PartialMachine :=
  d1LiveAfter02And14.map d1Child

theorem d102_same_source :
    d1Child ⟨false,false,2⟩ = BB6.Agent29Raw36D102.b1 := by rfl

theorem d114_same_source :
    d1Child ⟨true,false,2⟩ = BB6.Agent29Raw36D114.b1 := by rfl

theorem d102_cover_at (B : Nat) (hB : 172 ≤ B) :
    Cover (WeightedBound B) (d1Child ⟨false,false,2⟩) := by
  rw [d102_same_source]
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans (BB6.Agent29Raw36D102.bound m hm k d hk hd) hB

theorem d114_cover_at (B : Nat) (hB : 366 ≤ B) :
    Cover (WeightedBound B) (d1Child ⟨true,false,2⟩) := by
  rw [d114_same_source]
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans (BB6.Agent29Raw36D114.bound m hm k d hk hd) hB

theorem parent_cover_from_live7_after02And14 (B : Nat) (hB : 1152 ≤ B)
    (h : ∀ p ∈ parentLiveAfter02And14, Cover (WeightedBound B) p) :
    Cover (WeightedBound B) parent := by
  apply parent_cover_from_nine B hB
  intro p hp
  unfold parentLive9 at hp
  rcases List.mem_map.mp hp with ⟨mv,hm,rfl⟩
  simp only [d1Complement, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact d102_cover_at B (by omega)
  · exact d114_cover_at B (by omega)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact h _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)

theorem after02And14_count :
    parentLiveAfter02And14.length = 7 := by decide

#print axioms d102_same_source
#print axioms d114_same_source
#print axioms d102_cover_at
#print axioms d114_cover_at
#print axioms parent_cover_from_live7_after02And14
#print axioms after02And14_count
end BB6.Agent29Raw36
