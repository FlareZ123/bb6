import Raw56Root15
import Raw56PilotE10RBAll

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw56Root
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

/-- A sixth certified E1 sibling, E1=0RB, is removed from the literal
    Raw56 root frontier; fourteen cases remain. -/
def remaining14RDRB :=
  remaining15RDLC.filter (fun e => !sameTable e.2 BB6.Agent1Raw56Pilot.E10RB.p)

theorem count14RDRB : remaining14RDRB.length = 14 := by decide

theorem sound14RDRB :
    ∀ m, TNFQuotientCompatible parent m →
      WeightedBound 14000 m ∨
        ∃ e ∈ remaining14RDRB, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound15RDLC m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · by_cases hmatch : sameTable e.2 BB6.Agent1Raw56Pilot.E10RB.p = true
    · have hEq : e.2 = BB6.Agent1Raw56Pilot.E10RB.p := sameTable_sound hmatch
      exact Or.inl (BB6.Agent1Raw56Pilot.E10RB.all_quotient m (hEq ▸ hq))
    · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hmatch]⟩,hq⟩

#print axioms count14RDRB
#print axioms sound14RDRB
end BB6.Agent1Raw56Root
