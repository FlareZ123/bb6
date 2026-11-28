import Raw56Root17
import Raw56LBComplete

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent4Raw56Root16LB
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

/-- Consume the complete E1=1LB original-source sibling Cover against the
    independently accepted 17-way Raw56 root frontier.  This is a *local*
    Raw56 reduction; it does not discharge Canonical39 or BB(6). -/
def remaining16LB :=
  BB6.Agent1Raw56Root.remaining17RCRE.filter
    (fun e => !sameTable e.2 BB6.Agent4Raw56LB.E11LB.p)

theorem count16LB : remaining16LB.length = 16 := by decide

theorem sound16LB :
    ∀ m, TNFQuotientCompatible BB6.Agent1Raw56Root.parent m →
      WeightedBound 1000000 m ∨
        ∃ e ∈ remaining16LB, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent1Raw56Root.sound17RCRE m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · by_cases hmatch : sameTable e.2 BB6.Agent4Raw56LB.E11LB.p = true
    · have hEq : e.2 = BB6.Agent4Raw56LB.E11LB.p := sameTable_sound hmatch
      exact Or.inl (BB6.Agent4Raw56LB.E11LB.all_quotient m (hEq ▸ hq))
    · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hmatch]⟩,hq⟩

#print axioms count16LB
#print axioms sound16LB
end BB6.Agent4Raw56Root16LB
