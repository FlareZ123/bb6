import Raw49Progress97
import Raw49C15All
import Raw49C29All
import Raw49C44All
import Raw49C48All
import Raw49C52All
import Raw49C54All
import Raw49C55All
import Raw49C57All
import Raw49C60All
import Raw49C61All
import Raw49C62All
import Raw49C64All
import Raw49C65All
import Raw49C67All
import Raw49C68All
import Raw49C69All
import Raw49C70All
import Raw49C73All
import Raw49C74All
import Raw49C75All
import Raw49C76All
import Raw49C77All
import Raw49C78All
import Raw49C82All
import Raw49C83All
import Raw49C84All
import Raw49C85All
import Raw49C86All
import Raw49C88All
import Raw49C89All
import Raw49C93All
import Raw49C94All
import Raw49C100All
import Raw49C105All
import Raw49C111All
import Raw49C114All
import Raw49C115All
import Raw49C119All
import Raw49C123All
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49Progress58
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier
open BB6.Agent7Raw49Cut

def closedTables : List PartialMachine := [BB6.Agent7.Raw49C15.p,BB6.Agent7.Raw49C29.p,BB6.Agent7.Raw49C44.p,BB6.Agent7.Raw49C48.p,BB6.Agent7.Raw49C52.p,BB6.Agent7.Raw49C54.p,BB6.Agent7.Raw49C55.p,BB6.Agent7.Raw49C57.p,BB6.Agent7.Raw49C60.p,BB6.Agent7.Raw49C61.p,BB6.Agent7.Raw49C62.p,BB6.Agent7.Raw49C64.p,BB6.Agent7.Raw49C65.p,BB6.Agent7.Raw49C67.p,BB6.Agent7.Raw49C68.p,BB6.Agent7.Raw49C69.p,BB6.Agent7.Raw49C70.p,BB6.Agent7.Raw49C73.p,BB6.Agent7.Raw49C74.p,BB6.Agent7.Raw49C75.p,BB6.Agent7.Raw49C76.p,BB6.Agent7.Raw49C77.p,BB6.Agent7.Raw49C78.p,BB6.Agent7.Raw49C82.p,BB6.Agent7.Raw49C83.p,BB6.Agent7.Raw49C84.p,BB6.Agent7.Raw49C85.p,BB6.Agent7.Raw49C86.p,BB6.Agent7.Raw49C88.p,BB6.Agent7.Raw49C89.p,BB6.Agent7.Raw49C93.p,BB6.Agent7.Raw49C94.p,BB6.Agent7.Raw49C100.p,BB6.Agent7.Raw49C105.p,BB6.Agent7.Raw49C111.p,BB6.Agent7.Raw49C114.p,BB6.Agent7.Raw49C115.p,BB6.Agent7.Raw49C119.p,BB6.Agent7.Raw49C123.p]
def removeClosed (p : PartialMachine) : Bool := closedTables.any (equalTable p)
def residuals := BB6.Agent7Raw49Progress97.residuals.filter (fun e => !removeClosed e.2)

theorem residual_count : residuals.length = 58 := by decide

theorem closedSafe (p : PartialMachine) (h : p ∈ closedTables) (m : Machine) (hm : TNFQuotientCompatible p m) : WeightedBound 7014 m := by
  simp only [closedTables,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact BB6.Agent7.Raw49C15.all_quotient m hm
  · exact BB6.Agent7.Raw49C29.all_quotient m hm
  · exact BB6.Agent7.Raw49C44.all_quotient m hm
  · exact BB6.Agent7.Raw49C48.all_quotient m hm
  · exact BB6.Agent7.Raw49C52.all_quotient m hm
  · exact BB6.Agent7.Raw49C54.all_quotient m hm
  · exact BB6.Agent7.Raw49C55.all_quotient m hm
  · exact BB6.Agent7.Raw49C57.all_quotient m hm
  · exact BB6.Agent7.Raw49C60.all_quotient m hm
  · exact BB6.Agent7.Raw49C61.all_quotient m hm
  · exact BB6.Agent7.Raw49C62.all_quotient m hm
  · exact BB6.Agent7.Raw49C64.all_quotient m hm
  · exact BB6.Agent7.Raw49C65.all_quotient m hm
  · exact BB6.Agent7.Raw49C67.all_quotient m hm
  · exact BB6.Agent7.Raw49C68.all_quotient m hm
  · exact BB6.Agent7.Raw49C69.all_quotient m hm
  · exact BB6.Agent7.Raw49C70.all_quotient m hm
  · exact BB6.Agent7.Raw49C73.all_quotient m hm
  · exact BB6.Agent7.Raw49C74.all_quotient m hm
  · exact BB6.Agent7.Raw49C75.all_quotient m hm
  · exact BB6.Agent7.Raw49C76.all_quotient m hm
  · exact BB6.Agent7.Raw49C77.all_quotient m hm
  · exact BB6.Agent7.Raw49C78.all_quotient m hm
  · exact BB6.Agent7.Raw49C82.all_quotient m hm
  · exact BB6.Agent7.Raw49C83.all_quotient m hm
  · exact BB6.Agent7.Raw49C84.all_quotient m hm
  · exact BB6.Agent7.Raw49C85.all_quotient m hm
  · exact BB6.Agent7.Raw49C86.all_quotient m hm
  · exact BB6.Agent7.Raw49C88.all_quotient m hm
  · exact BB6.Agent7.Raw49C89.all_quotient m hm
  · exact BB6.Agent7.Raw49C93.all_quotient m hm
  · exact BB6.Agent7.Raw49C94.all_quotient m hm
  · exact BB6.Agent7.Raw49C100.all_quotient m hm
  · exact BB6.Agent7.Raw49C105.all_quotient m hm
  · exact BB6.Agent7.Raw49C111.all_quotient m hm
  · exact BB6.Agent7.Raw49C114.all_quotient m hm
  · exact BB6.Agent7.Raw49C115.all_quotient m hm
  · exact BB6.Agent7.Raw49C119.all_quotient m hm
  · exact BB6.Agent7.Raw49C123.all_quotient m hm

theorem refined (m : Machine) (hm : TNFQuotientCompatible parent m) : WeightedBound 7014 m ∨ ∃ e ∈ residuals, TNFQuotientCompatible e.2 m := by
  rcases BB6.Agent7Raw49Progress97.refined m hm with h | ⟨e,he,hq⟩
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
end BB6.Agent7Raw49Progress58
