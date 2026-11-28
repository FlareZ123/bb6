import Raw36ParentLive6D101
import Raw36D110Live6AfterE0LE1LB

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Expose the D110 (= D1=0RE) nested decomposition through Agent18's current
six-live Raw36 parent interface.  Five direct D1 Cover premises remain,
while the D1=0RE premise is replaced by the six live first-E0 Cover
premises of the source-checked D110 reduction.  This is conditional:
the D110 child Covers are explicit hypotheses, not discharged here.
-/

namespace BB6.Agent29Raw36D110Parent
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent29Raw36

def d1LiveAfterD110 : List Move := [
  ⟨false,false,0⟩, ⟨true,false,0⟩, ⟨false,false,4⟩,
  ⟨true,false,4⟩, ⟨true,true,4⟩]

def parentLiveAfterD110 : List PartialMachine :=
  d1LiveAfterD110.map d1Child

theorem d110_same_source :
    d1Child ⟨false,true,4⟩ =
      BB6.Agent29Raw36D110Live8.parent := by rfl

theorem d110_cover_from_six_nested
    (hE0 : ∀ i ∈ BB6.Agent29Raw36D110Live6.liveCodes,
      Cover (WeightedBound 2004)
        (BB6.Agent29Raw36D110Live8.child i)) :
    Cover (WeightedBound 2004) (d1Child ⟨false,true,4⟩) := by
  rw [d110_same_source]
  exact BB6.Agent29Raw36D110Live6.parent_cover_from_live6 hE0

theorem parent_cover_from_five_direct_and_six_nested
    (hD1 : ∀ p ∈ parentLiveAfterD110,
      Cover (WeightedBound 2004) p)
    (hE0 : ∀ i ∈ BB6.Agent29Raw36D110Live6.liveCodes,
      Cover (WeightedBound 2004)
        (BB6.Agent29Raw36D110Live8.child i)) :
    Cover (WeightedBound 2004) BB6.Agent29Raw36.parent := by
  apply BB6.Agent18Raw36.parent_cover_from_live6_after01_02_14 2004 (by omega)
  intro p hp
  unfold BB6.Agent18Raw36.parentLiveAfter01_02_14 at hp
  rcases List.mem_map.mp hp with ⟨mv,hm,rfl⟩
  simp only [BB6.Agent18Raw36.d1LiveAfter01_02_14,
    List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hD1 _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact hD1 _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact hD1 _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact d110_cover_from_six_nested hE0
  · exact hD1 _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)
  · exact hD1 _ (List.mem_map.mpr ⟨_,by decide,rfl⟩)

theorem direct_live_count : parentLiveAfterD110.length = 5 := by decide

theorem nested_live_count :
    BB6.Agent29Raw36D110Live6.liveCodes.length = 6 := by decide

#print axioms d110_same_source
#print axioms d110_cover_from_six_nested
#print axioms parent_cover_from_five_direct_and_six_nested
#print axioms direct_live_count
#print axioms nested_live_count
end BB6.Agent29Raw36D110Parent
