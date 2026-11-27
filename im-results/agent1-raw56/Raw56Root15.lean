import Raw56Root17
import Raw56PilotE10RDAll
import Raw56PilotE11LCAll

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw56Root
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

def remaining16RD :=
  remaining17RCRE.filter (fun e => !sameTable e.2 BB6.Agent1Raw56Pilot.E10RD.p)

theorem count16RD : remaining16RD.length = 16 := by decide

theorem sound16RD :
    ∀ m, TNFQuotientCompatible parent m →
      WeightedBound 12000 m ∨
        ∃ e ∈ remaining16RD, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound17RCRE m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · by_cases hmatch : sameTable e.2 BB6.Agent1Raw56Pilot.E10RD.p = true
    · have hEq : e.2 = BB6.Agent1Raw56Pilot.E10RD.p := sameTable_sound hmatch
      exact Or.inl (BB6.Agent1Raw56Pilot.E10RD.all_quotient m (hEq ▸ hq))
    · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hmatch]⟩,hq⟩

def remaining15RDLC :=
  remaining16RD.filter (fun e => !sameTable e.2 BB6.Agent1Raw56Pilot.E11LC.p)

theorem count15RDLC : remaining15RDLC.length = 15 := by decide

theorem sound15RDLC :
    ∀ m, TNFQuotientCompatible parent m →
      WeightedBound 12000 m ∨
        ∃ e ∈ remaining15RDLC, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound16RD m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases hmatch : sameTable e.2 BB6.Agent1Raw56Pilot.E11LC.p = true
    · have hEq : e.2 = BB6.Agent1Raw56Pilot.E11LC.p := sameTable_sound hmatch
      exact Or.inl (BB6.Agent1Raw56Pilot.E11LC.all_quotient m (hEq ▸ hq))
    · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hmatch]⟩,hq⟩

#print axioms count16RD
#print axioms sound16RD
#print axioms count15RDLC
#print axioms sound15RDLC
end BB6.Agent1Raw56Root
