import Raw49Progress112
import Raw49C9All
import Raw49C10All
import Raw49C11All
import Raw49C12All
import Raw49C13All
import Raw49C14All
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49Progress106
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier
open BB6.Agent7Raw49Cut

def closedTables : List PartialMachine := [BB6.Agent7.Raw49C9.p,BB6.Agent7.Raw49C10.p,BB6.Agent7.Raw49C11.p,BB6.Agent7.Raw49C12.p,BB6.Agent7.Raw49C13.p,BB6.Agent7.Raw49C14.p]
def removeClosed (p : PartialMachine) : Bool := closedTables.any (equalTable p)
def residuals := BB6.Agent7Raw49Progress112.residuals.filter (fun e => !removeClosed e.2)

theorem residual_count : residuals.length = 106 := by decide

theorem closedSafe (p : PartialMachine) (h : p ∈ closedTables) (m : Machine) (hm : TNFQuotientCompatible p m) : WeightedBound 7014 m := by
  simp only [closedTables,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact BB6.Agent7.Raw49C9.all_quotient m hm
  · exact BB6.Agent7.Raw49C10.all_quotient m hm
  · exact BB6.Agent7.Raw49C11.all_quotient m hm
  · exact BB6.Agent7.Raw49C12.all_quotient m hm
  · exact BB6.Agent7.Raw49C13.all_quotient m hm
  · exact BB6.Agent7.Raw49C14.all_quotient m hm

theorem refined (m : Machine) (hm : TNFQuotientCompatible parent m) : WeightedBound 7014 m ∨ ∃ e ∈ residuals, TNFQuotientCompatible e.2 m := by
  rcases BB6.Agent7Raw49Progress112.refined m hm with h | ⟨e,he,hq⟩
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
end BB6.Agent7Raw49Progress106
