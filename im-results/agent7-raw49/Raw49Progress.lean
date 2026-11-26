import Raw49Cut
import Raw49C0All
import Raw49C5All
import Raw49C2All
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49Progress
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier
open BB6.Agent7Raw49Cut

def closedTables : List PartialMachine := [BB6.Agent7.Raw49C0.p,BB6.Agent7.Raw49C5.p,BB6.Agent7.Raw49C2.p]
def removeClosed (p : PartialMachine) : Bool := closedTables.any (equalTable p)
def residuals := remaining.filter (fun e => !removeClosed e.2)

theorem residual_count : residuals.length = 118 := by decide

theorem closedSafe (p : PartialMachine) (h : p ∈ closedTables) (m : Machine) (hm : TNFQuotientCompatible p m) : WeightedBound 7014 m := by
  simp only [closedTables,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with rfl|rfl|rfl
  · exact BB6.Agent7.Raw49C0.all_quotient m hm
  · exact BB6.Agent7.Raw49C5.all_quotient m hm
  · exact BB6.Agent7.Raw49C2.all_quotient m hm

theorem refined (m : Machine) (hm : TNFQuotientCompatible parent m) : WeightedBound 7014 m ∨ ∃ e ∈ residuals, TNFQuotientCompatible e.2 m := by
  rcases parent_cut m hm with h | ⟨e,he,hq⟩
  · exact Or.inl h
  · cases hh : removeClosed e.2 with
    | false => exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hh]⟩,hq⟩
    | true =>
      obtain ⟨p,hp,hmatch⟩ := List.any_eq_true.mp hh
      have eq := equalTable_sound hmatch
      rw [eq] at hq
      exact Or.inl (closedSafe p hp m hq)

#print axioms refined
#print axioms residual_count
end BB6.Agent7Raw49Progress
