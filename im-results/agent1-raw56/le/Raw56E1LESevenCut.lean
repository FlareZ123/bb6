import Raw56E1LEFiveCut

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw56E1LE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

/-- Unproved E0=0RA and 0LF siblings of E1=0LE, represented by their authentic
    source tables. Their subsequent canonical subfronters are kept explicit. -/
def raPartial : PartialMachine := refine p (4,false) (some ⟨false,true,0⟩)
def lfPartial : PartialMachine := refine p (4,false) (some ⟨false,false,5⟩)
def remaining7 := remaining9.filter (fun e =>
  (!sameTable e.2 raPartial) && (!sameTable e.2 lfPartial))

theorem count7 : remaining7.length = 7 := by decide

/-- Reusable conditional source-root composition: seven first-query siblings
    together with the exact residual subfamilies of the two independently
    classified E0 children. This theorem never assumes either child's
    residuals empty. -/
theorem sound7
    (hRB : ∀ m, TNFQuotientCompatible rb m → WeightedBound 7014 m)
    (hRC : ∀ m, TNFQuotientCompatible rc m → WeightedBound 7014 m)
    (hLB : ∀ m, TNFQuotientCompatible lb m → WeightedBound 7014 m)
    (hLA : ∀ m, TNFQuotientCompatible la m → WeightedBound 7014 m)
    (hRA : ∀ m, TNFQuotientCompatible ra m → WeightedBound 14000 m)
    (rra rlf : List (Nat × PartialMachine))
    (hRAPartial : ∀ m, TNFQuotientCompatible raPartial m →
      WeightedBound 7014 m ∨ ∃ e ∈ rra, TNFQuotientCompatible e.2 m)
    (hLFPartial : ∀ m, TNFQuotientCompatible lfPartial m →
      WeightedBound 40000 m ∨ ∃ e ∈ rlf, TNFQuotientCompatible e.2 m) :
    ∀ m, TNFQuotientCompatible p m →
      WeightedBound 40000 m ∨
      (∃ e ∈ remaining7, TNFQuotientCompatible e.2 m) ∨
      (∃ e ∈ rra, TNFQuotientCompatible e.2 m) ∨
      (∃ e ∈ rlf, TNFQuotientCompatible e.2 m) := by
  intro m hm
  rcases sound9 hRB hRC hLB hLA hRA m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · by_cases hmatchRA : sameTable e.2 raPartial = true
    · have heq : e.2 = raPartial := sameTable_sound hmatchRA
      rcases hRAPartial m (heq ▸ hq) with hb | ⟨x,hx,hqx⟩
      · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
      · exact Or.inr (Or.inr (Or.inl ⟨x,hx,hqx⟩))
    · by_cases hmatchLF : sameTable e.2 lfPartial = true
      · have heq : e.2 = lfPartial := sameTable_sound hmatchLF
        rcases hLFPartial m (heq ▸ hq) with hb | ⟨x,hx,hqx⟩
        · exact Or.inl hb
        · exact Or.inr (Or.inr (Or.inr ⟨x,hx,hqx⟩))
      · exact Or.inr (Or.inl ⟨e,List.mem_filter.mpr
          ⟨he,by simp [hmatchRA,hmatchLF]⟩,hq⟩)

#print axioms count7
#print axioms sound7
end BB6.Agent1Raw56E1LE
