import Raw56E1LEFourCut
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw56E1LE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

def remaining11 := remaining12.filter (fun e => !sameTable e.2 lb)
theorem count11 : remaining11.length = 11 := by decide
theorem sound11
    (hRB : ∀ m, TNFQuotientCompatible rb m → WeightedBound 7014 m)
    (hRC : ∀ m, TNFQuotientCompatible rc m → WeightedBound 7014 m)
    (hLB : ∀ m, TNFQuotientCompatible lb m → WeightedBound 7014 m) :
    ∀ m, TNFQuotientCompatible p m →
      WeightedBound 7014 m ∨ ∃ e ∈ remaining11, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound12 hRB hRC m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases hmatch : sameTable e.2 lb = true
    · have heq : e.2 = lb := sameTable_sound hmatch
      exact Or.inl (hLB m (heq ▸ hq))
    · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hmatch]⟩,hq⟩

#print axioms sound11
end BB6.Agent1Raw56E1LE
