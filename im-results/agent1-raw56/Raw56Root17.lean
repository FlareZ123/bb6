import Raw56E1RCAll
import Raw56REParentConsumer

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw56Root
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

/-- The accepted E1=0RC and E1=1RE Covers are distinct members of the
    already accepted Raw56 19-way root frontier. Removing both leaves exactly
    seventeen literal representatives. -/
def remaining17RCRE :=
  remaining18RC.filter (fun e => !sameTable e.2 BB6.Agent4Raw56REParent.p)

theorem count17RCRE : remaining17RCRE.length = 17 := by decide

theorem sound17RCRE :
    ∀ m, TNFQuotientCompatible parent m →
      WeightedBound 10000 m ∨
        ∃ e ∈ remaining17RCRE, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound18RC_closed m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases hmatch : sameTable e.2 BB6.Agent4Raw56REParent.p = true
    · have hEq : e.2 = BB6.Agent4Raw56REParent.p := sameTable_sound hmatch
      exact Or.inl (BB6.Agent4Raw56REParent.all_quotient m (hEq ▸ hq))
    · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hmatch]⟩,hq⟩

#print axioms count17RCRE
#print axioms sound17RCRE
end BB6.Agent1Raw56Root
