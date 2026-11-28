import Raw56E1LEFiveCut

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw56E1LE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

/-- Sixth complete E0 sibling candidate: E0=0LF. Its exact complete child
    theorem has threshold 40000, so the composed frontier uses that bound. -/
def lf : PartialMachine := refine p (4,false) (some ⟨false,false,5⟩)
def remaining8 := remaining9.filter (fun e => !sameTable e.2 lf)
theorem count8 : remaining8.length = 8 := by decide

theorem sound8
    (hRB : ∀ m, TNFQuotientCompatible rb m → WeightedBound 7014 m)
    (hRC : ∀ m, TNFQuotientCompatible rc m → WeightedBound 7014 m)
    (hLB : ∀ m, TNFQuotientCompatible lb m → WeightedBound 7014 m)
    (hLA : ∀ m, TNFQuotientCompatible la m → WeightedBound 7014 m)
    (hRA : ∀ m, TNFQuotientCompatible ra m → WeightedBound 14000 m)
    (hLF : ∀ m, TNFQuotientCompatible lf m → WeightedBound 40000 m) :
    ∀ m, TNFQuotientCompatible p m →
      WeightedBound 40000 m ∨ ∃ e ∈ remaining8, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound9 hRB hRC hLB hLA hRA m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · by_cases hmatch : sameTable e.2 lf = true
    · have heq : e.2 = lf := sameTable_sound hmatch
      exact Or.inl (hLF m (heq ▸ hq))
    · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hmatch]⟩,hq⟩

#print axioms count8
#print axioms sound8
end BB6.Agent1Raw56E1LE
