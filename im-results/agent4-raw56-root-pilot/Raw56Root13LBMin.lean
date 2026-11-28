import Raw56Root14
import Raw56LBCompleteMin

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent4Raw56Root13LB
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

/-- Conditional exact Raw56 14-to-13 frontier reduction: the entire
    E1=1LB six-hole sibling is discharged by its independently certified
    exhaustive canonical tree plus six literal nonhalting residuals. -/
def remaining13LB :=
  BB6.Agent1Raw56Root.remaining14RDRB.filter
    (fun e => !sameTable e.2 BB6.Agent4Raw56LB.E11LB.p)

theorem count13LB : remaining13LB.length = 13 := by decide

theorem sound13LB :
    ∀ m, TNFQuotientCompatible BB6.Agent1Raw56Root.parent m →
      WeightedBound 1000000 m ∨
        ∃ e ∈ remaining13LB, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent1Raw56Root.sound14RDRB m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · by_cases hmatch : sameTable e.2 BB6.Agent4Raw56LB.E11LB.p = true
    · have hEq : e.2 = BB6.Agent4Raw56LB.E11LB.p := sameTable_sound hmatch
      exact Or.inl (BB6.Agent4Raw56LB.E11LB.all_quotient m (hEq ▸ hq))
    · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hmatch]⟩,hq⟩

#print axioms count13LB
#print axioms sound13LB
end BB6.Agent4Raw56Root13LB
