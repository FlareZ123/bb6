import CThreeSixAllCriterion
import OddOddConeSource
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0

namespace BB6.Agent2COddOddIntegration

/-- The established strongest both-branch six-forced Machine C criterion
    extended by the new source-exact 48/64 odd-odd high-stop exclusion. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11SixAll.highAllowed j m ∧
  ¬ (5≤m ∧ m%4=1 ∧ j%64=(3*m+50)%64)

private theorem power_lower (m : Nat) : 4*m+4≤2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show 2*(m+1)+2=2*m+2+2 by omega, Nat.pow_add]
    change 4*(m+1)+4 ≤ 2^(2*m+2)*4
    omega

private theorem high_bound (j m : Nat) :
    j+3*m+5≤2^(2*m+2)*(j+3) := by
  have hb := power_lower m
  have hp : 1≤2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j≤2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  have hm : 3*m+5≤2^(2*m+2)*3 := by
    have h3 := Nat.mul_le_mul_right 3 hb
    omega
  rw [Nat.mul_add]
  omega

/-- Lossless original-blank Machine C halting equivalence: the new
    infinite high index lattice is removed without modifying either root
    decider or any previous source-certified high/low restrictions. -/
theorem blank_halts_iff_six_oddodd :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11SixAll.lowAllowed m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11SixAll.blank_halts_iff_six_both]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hn : ¬(5≤m ∧ m%4=1 ∧ j%64=(3*m+50)%64) := by
        rintro ⟨hm5,hm4,hj64⟩
        have hr : BB6.Agent3.CReach (2*j+3) k :=
          (BB6.Agent11SixForced.sixForcedRootDecision_iff (2*j+3) k).mp hroot
        have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
          dsimp [k]
          have hc := Nat.sub_add_cancel (high_bound j m)
          omega
        rcases hr with ⟨time,ht⟩
        exact (BB6.Agent2COddOddCone.high_stop_blank_unreachable
          j m k hm5 hm4 hj64 hstop time) ht
      exact Or.inr ⟨j,m,⟨hprior,hn⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms blank_halts_iff_six_oddodd

end BB6.Agent2COddOddIntegration
