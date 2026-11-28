import Raw40SixFamilyRefinement
import Raw40A1LC

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42Raw40SevenFamilyRefinement
open BB6Coverage BB6.Agent47CanonicalFrontier

def inA1LC (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A1LC.bounds.any fun x =>
    BB6.Agent19Raw40.A1LC.equalTable e.2 (BB6.Agent19Raw40.A1LC.child x.1)

/-- Candidate Raw40 canonical frontier after composing seven complete
    six-hole first-query families. -/
def remaining : List (List Move × PartialMachine) :=
  BB6.Agent42Raw40SixFamilyRefinement.remaining.filter fun e => ! inA1LC e

/-- A1=1LC removes twelve additional canonical five-hole residuals. -/
theorem count : remaining.length = 104 := by decide

theorem sound :
    ∀ m, TNFQuotientCompatible BB6.Agent19Raw40.parent m →
      WeightedBound 22169 m ∨
        ∃ e ∈ remaining, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent42Raw40SixFamilyRefinement.sound m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases h : inA1LC e = true
    · left
      unfold inA1LC at h
      obtain ⟨x,hx,heq⟩ := List.any_eq_true.mp h
      have eq : e.2 = BB6.Agent19Raw40.A1LC.child x.1 :=
        BB6.Agent19Raw40.A1LC.equalTable_sound _ _ heq
      have hb := BB6.Agent19Raw40.A1LC.children x hx m (eq ▸ hq)
      have hB : x.2 ≤ 7863 :=
        of_decide_eq_true (List.all_eq_true.mp BB6.Agent19Raw40.A1LC.boundOK x hx)
      intro n d hn hd
      exact Nat.le_trans (hb n d hn hd) (Nat.le_trans hB (by omega))
    · right
      have hf : inA1LC e = false := by
        cases hx : inA1LC e
        · rfl
        · exact (h hx).elim
      refine ⟨e, ?_, hq⟩
      simp [remaining, he, hf]

#print axioms count
#print axioms sound
end BB6.Agent42Raw40SevenFamilyRefinement
