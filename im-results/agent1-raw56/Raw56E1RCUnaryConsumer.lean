import Raw56E1RCCut
import Raw56RC0RDAll
import Raw56RC1LEAll
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw56E1RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

def rd0 : PartialMachine := refine p (2,true) (some ⟨false,true,3⟩)
def le1 : PartialMachine := refine p (2,true) (some ⟨true,false,4⟩)
theorem rd0_eq : BB6.Agent1Raw56.RC0RD.p = rd0 := sameTable_sound (by decide)
theorem le1_eq : BB6.Agent1Raw56.RC1LE.p = le1 := sameTable_sound (by decide)

def remaining16 := (remaining18.filter (fun e => !sameTable e.2 rd0)).filter (fun e => !sameTable e.2 le1)
theorem count16 : remaining16.length = 16 := by decide

theorem sound16 (hRD : ∀ m, TNFQuotientCompatible rd m → WeightedBound 7014 m) :
    ∀ m, TNFQuotientCompatible p m →
      WeightedBound 7014 m ∨ ∃ e ∈ remaining16, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound18 hRD m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases h0 : sameTable e.2 rd0 = true
    · have heq : e.2 = rd0 := sameTable_sound h0
      exact Or.inl (BB6.Agent1Raw56.RC0RD.all_quotient m (rd0_eq.symm ▸ (heq ▸ hq)))
    · by_cases h1 : sameTable e.2 le1 = true
      · have heq : e.2 = le1 := sameTable_sound h1
        exact Or.inl (BB6.Agent1Raw56.RC1LE.all_quotient m (le1_eq.symm ▸ (heq ▸ hq)))
      · exact Or.inr ⟨e,List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨he,by simp [h0]⟩,by simp [h1]⟩,hq⟩
#print axioms rd0_eq
#print axioms le1_eq
#print axioms count16
#print axioms sound16
end BB6.Agent1Raw56E1RC
