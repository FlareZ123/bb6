import Raw49Progress
import Raw49C3All
import Raw49C4All
import Raw49C8All
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49Progress115
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier
open BB6.Agent7Raw49Cut

def closedTables : List PartialMachine := [BB6.Agent7.Raw49C3.p,BB6.Agent7.Raw49C4.p,BB6.Agent7.Raw49C8.p]
def removeClosed (p : PartialMachine) : Bool := closedTables.any (equalTable p)
def residuals := BB6.Agent7Raw49Progress.residuals.filter (fun e => !removeClosed e.2)

theorem residual_count : residuals.length = 115 := by decide

theorem closedSafe (p : PartialMachine) (h : p ∈ closedTables) (m : Machine) (hm : TNFQuotientCompatible p m) : WeightedBound 7014 m := by
  simp only [closedTables,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with rfl|rfl|rfl
  · exact BB6.Agent7.Raw49C3.all_quotient m hm
  · exact BB6.Agent7.Raw49C4.all_quotient m hm
  · exact BB6.Agent7.Raw49C8.all_quotient m hm

theorem refined (m : Machine) (hm : TNFQuotientCompatible parent m) : WeightedBound 7014 m ∨ ∃ e ∈ residuals, TNFQuotientCompatible e.2 m := by
  rcases BB6.Agent7Raw49Progress.refined m hm with h | ⟨e,he,hq⟩
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
end BB6.Agent7Raw49Progress115
