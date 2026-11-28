import Raw40FiveFamilyRefinement
import Raw40A1LB

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42Raw40SixFamilyRefinement
open BB6Coverage BB6.Agent47CanonicalFrontier

def inA1LB (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A1LB.bounds.any fun x =>
    BB6.Agent19Raw40.A1LB.equalTable e.2 (BB6.Agent19Raw40.A1LB.child x.1)

/-- Raw40's canonical frontier after adding the complete A1=1LB family to
    the five-family refinement. -/
def remaining : List (List Move × PartialMachine) :=
  BB6.Agent42Raw40FiveFamilyRefinement.remaining.filter fun e => ! inA1LB e

/-- The A1=1LB family accounts for sixteen more residuals, reducing the
    already-composed 132-entry frontier to 116. -/
theorem count : remaining.length = 116 := by decide

theorem sound :
    ∀ m, TNFQuotientCompatible BB6.Agent19Raw40.parent m →
      WeightedBound 22169 m ∨
        ∃ e ∈ remaining, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent42Raw40FiveFamilyRefinement.sound m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases h : inA1LB e = true
    · left
      unfold inA1LB at h
      obtain ⟨x,hx,heq⟩ := List.any_eq_true.mp h
      have eq : e.2 = BB6.Agent19Raw40.A1LB.child x.1 :=
        BB6.Agent19Raw40.A1LB.equalTable_sound _ _ heq
      have hb := BB6.Agent19Raw40.A1LB.children x hx m (eq ▸ hq)
      have hB : x.2 ≤ 19585 :=
        of_decide_eq_true (List.all_eq_true.mp BB6.Agent19Raw40.A1LB.boundOK x hx)
      intro n d hn hd
      exact Nat.le_trans (hb n d hn hd) (Nat.le_trans hB (by omega))
    · right
      have hf : inA1LB e = false := by
        cases hx : inA1LB e
        · rfl
        · exact (h hx).elim
      refine ⟨e, ?_, hq⟩
      simp [remaining, he, hf]

#print axioms count
#print axioms sound
end BB6.Agent42Raw40SixFamilyRefinement
