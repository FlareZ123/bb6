import Raw56E1LECut
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw56E1LE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

/-- The remaining E0=0LB literal branch of E1=0LE. -/
def lb : PartialMachine := refine p (4,false) (some ⟨false,false,1⟩)
/-- The remaining E0=1LA literal branch of E1=0LE. -/
def la : PartialMachine := refine p (4,false) (some ⟨true,false,0⟩)

def remaining10 := remaining12.filter (fun e => !(sameTable e.2 lb || sameTable e.2 la))
theorem count10 : remaining10.length = 10 := by decide

theorem sound10
    (hRB : ∀ m, TNFQuotientCompatible rb m → WeightedBound 7014 m)
    (hRC : ∀ m, TNFQuotientCompatible rc m → WeightedBound 7014 m)
    (hLB : ∀ m, TNFQuotientCompatible lb m → WeightedBound 7014 m)
    (hLA : ∀ m, TNFQuotientCompatible la m → WeightedBound 7014 m) :
    ∀ m, TNFQuotientCompatible p m →
      WeightedBound 7014 m ∨ ∃ e ∈ remaining10, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound12 hRB hRC m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases hmatch : sameTable e.2 lb = true
    · have heq : e.2 = lb := sameTable_sound hmatch
      exact Or.inl (hLB m (heq ▸ hq))
    · by_cases hmatch' : sameTable e.2 la = true
      · have heq : e.2 = la := sameTable_sound hmatch'
        exact Or.inl (hLA m (heq ▸ hq))
      · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hmatch,hmatch']⟩,hq⟩

#print axioms sound10
end BB6.Agent1Raw56E1LE
