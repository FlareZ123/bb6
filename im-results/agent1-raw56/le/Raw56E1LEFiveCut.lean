import Raw56E1LEFourCut
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw56E1LE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

/-- E0=1RA requires a larger bound because the search has a late query. -/
def ra : PartialMachine := refine p (4,false) (some ⟨true,true,0⟩)
def remaining9 := remaining10.filter (fun e => !sameTable e.2 ra)
theorem count9 : remaining9.length = 9 := by decide

theorem sound9
    (hRB : ∀ m, TNFQuotientCompatible rb m → WeightedBound 7014 m)
    (hRC : ∀ m, TNFQuotientCompatible rc m → WeightedBound 7014 m)
    (hLB : ∀ m, TNFQuotientCompatible lb m → WeightedBound 7014 m)
    (hLA : ∀ m, TNFQuotientCompatible la m → WeightedBound 7014 m)
    (hRA : ∀ m, TNFQuotientCompatible ra m → WeightedBound 14000 m) :
    ∀ m, TNFQuotientCompatible p m →
      WeightedBound 14000 m ∨ ∃ e ∈ remaining9, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound10 hRB hRC hLB hLA m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · by_cases hmatch : sameTable e.2 ra = true
    · have heq : e.2 = ra := sameTable_sound hmatch
      exact Or.inl (hRA m (heq ▸ hq))
    · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hmatch]⟩,hq⟩

#print axioms sound9
end BB6.Agent1Raw56E1LE
