import Raw36Symmetry

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47PartialAudit

/-- The twenty genuinely different C1 choices after identifying the
    two still-unused machine labels E and F. -/
def representatives : List Move :=
  [⟨false,false,0⟩,
   ⟨false,false,1⟩,
   ⟨false,false,2⟩,
   ⟨false,false,3⟩,
   ⟨false,false,4⟩,
   ⟨false,true,0⟩,
   ⟨false,true,1⟩,
   ⟨false,true,2⟩,
   ⟨false,true,3⟩,
   ⟨false,true,4⟩,
   ⟨true,false,0⟩,
   ⟨true,false,1⟩,
   ⟨true,false,2⟩,
   ⟨true,false,3⟩,
   ⟨true,false,4⟩,
   ⟨true,true,0⟩,
   ⟨true,true,1⟩,
   ⟨true,true,2⟩,
   ⟨true,true,3⟩,
   ⟨true,true,4⟩]

theorem representatives_count : representatives.length = 20 := by decide
theorem representatives_nodup : representatives.Nodup := by decide

/-- Every physical C1 move is a representative, or is its E/F-swapped
    sibling. The proof exhausts the 24 real two-symbol successor moves. -/
theorem representative_class (mv : Move) :
    mv ∈ representatives ∨
      (mv.next = 5 ∧ ⟨mv.write,mv.right,4⟩ ∈ representatives) := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases w <;> cases r <;> decide

/-- A complete *source-exact* conditional classification of the six-hole
    Raw36 B1=0LA branch: twenty weighted child bounds suffice for all
    25^6 physical completions. The C1 halt choice is handled by the exact
    first-query partial audit; four F-target choices use state conjugacy. -/
theorem branch_bound_from_twenty (B : Nat) (hB : 162 ≤ B)
    (h : ∀ mv ∈ representatives, ∀ m,
      compatible (child mv) m → WeightedBound B m)
    (m : Machine) (hm : compatible branch m) : WeightedBound B m := by
  let t : PartialAudit := .split 9 (2,true) (fun _ => .unresolved)
  have hc : partialCheck 162 branch t = true := by
    rw [partialCheck.eq_3, Bool.and_eq_true]
    exact ⟨by decide, allMoves_of _ (by intro mv; rfl)⟩
  rcases partialSound 162 branch t branch_root branch_nohalt hc m hm with hb | ⟨e,he,hh⟩
  · intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) hB
  · rw [partialResiduals.eq_3] at he
    obtain ⟨mv,_,hmem⟩ := List.mem_flatMap.mp he
    rw [partialResiduals.eq_1] at hmem
    obtain ⟨e',he',heq⟩ := List.mem_map.mp hmem
    have he'' : e' = ([], child mv) := by
      simpa only [List.mem_singleton] using he'
    rw [← heq,he''] at hh
    rcases representative_class mv with hs | ⟨hq,hs⟩
    · exact h mv hs m hh
    · rcases mv with ⟨w,r,q⟩
      change q = 5 at hq
      subst q
      exact childF_bound B w r (h _ hs) m hh

/-- The companion Cover interface is directly composable with certificate
    producers. This theorem has no unresolved nonhalting assumptions: all
    premises are explicit child Covers. -/
theorem branch_cover_from_twenty (B : Nat) (hB : 162 ≤ B)
    (h : ∀ mv ∈ representatives, Cover (WeightedBound B) (child mv)) :
    Cover (WeightedBound B) branch := by
  apply Cover.leaf
  intro m hm
  exact branch_bound_from_twenty B hB
    (by intro mv hmv m hc; exact (h mv hmv).sound m hc) m hm

#print axioms representatives_count
#print axioms representative_class
#print axioms branch_bound_from_twenty
#print axioms branch_cover_from_twenty

end BB6.Agent29Raw36
