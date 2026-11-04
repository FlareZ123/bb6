import Back192BStep
import SourceBridge
import Agent46TerminalLifts
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0

namespace A4Backward192B

/-- Quantified reverse-core transport to the original checked-in CLine model. -/
theorem source_blank_never_bad192B (s : Nat × Nat × Nat)
    (h : BB6CLine.Reach s) : ¬ bad s.1 s.2.1 s.2.2 := by
  induction h with
  | init =>
      simp [bad, low]
  | next x y hx hstep ih =>
      rcases x with ⟨a,k,c⟩
      rcases y with ⟨a',k',c'⟩
      intro hb
      have he : A4Backward.nextC (a,k,c) = some (a',k',c') := by
        rw [A4Backward.nextC_source_equal]
        exact hstep
      exact ih (backward_step a k c a' k' c' he hb)

theorem source_no_83_13 (a k : Nat)
    (ha : a % 192 = 83) (hk : k % 192 = 13)
    (hr : BB6CLine.Reach (a,k,0)) : False := by
  exact source_blank_never_bad192B (a,k,0) hr
    (by simp [bad,low,ha,hk])

/-- Companion terminal cell, via the two original-source forced predecessors. -/
theorem source_no_179_109 (a k : Nat)
    (ha : a % 192 = 179) (hk : k % 192 = 109)
    (hr : BB6CLine.Reach (a,k,0)) : False := by
  have hlarge : 4 ≤ k := by omega
  have hp : BB6CLine.Reach (a,k-3,3) :=
    BB6.Agent46.reach_c0_two_parent a k hlarge hr
  have hnever := source_blank_never_bad192B (a,k-3,3) hp
  apply hnever
  simp only [bad,show ¬((3:Nat)<2) by omega,↓reduceIte,high]
  have hd : (a+96-3%96)%96=80 := by omega
  have ht : (a+(k-3))%192=93 := by omega
  right;right;right;right;right;right;right;right;right;right;right;right;right
  exact Or.inl ⟨hd, Or.inr ht⟩

#print axioms source_blank_never_bad192B
#print axioms source_no_83_13
#print axioms source_no_179_109

end A4Backward192B
