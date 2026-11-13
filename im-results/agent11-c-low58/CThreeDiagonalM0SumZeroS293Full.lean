import CThreeDiagonalM0SumZeroFull
import M0EvenEvenSumZeroS293
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0SumZeroS293Full

/-- Extend the current exact six-sector criterion by the new
    m=0, j=18791 mod 131072 exclusion. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11M0SumZeroAll.highAllowed j m ∧
  ¬(m=0 ∧ j%131072=18791)

private theorem high_bound (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hpow : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
  rw [Nat.mul_add]
  omega

private theorem high_stop_mzero_18791 (j k : Nat)
    (hj : j%131072=18791)
    (hstop : k+j+5=4*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  let w := (j-18791)/131072
  have hjform : j=18791+131072*w := by
    dsimp [w]
    omega
  have hkform : k=56380+393216*w := by
    rw [hjform] at hstop
    omega
  have hxform : 2*j+3=37585+262144*w := by
    rw [hjform]
    omega
  intro hr
  have hr' : BB6.Agent3.CReach
      (37585+262144*w) (56380+393216*w) := by
    simpa only [hxform,hkform] using hr
  exact BB6.Agent11M0SumZeroS293.blank_no_high_stop_s293 w hr'

/-- Lossless exact original-blank Machine C halting iff after excluding
    the new m=0, j=18791 mod 131072 high-stop cylinder. -/
theorem blank_halts_iff_six_mzero_sumzero_s293 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11SixAll.lowAllowed m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11M0SumZeroAll.blank_halts_iff_six_mzero_sumzero]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff (2*j+3) k).mp hroot
      have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (high_bound j m)
        omega
      have hnot : ¬(m=0 ∧ j%131072=18791) := by
        rintro ⟨hm,hj⟩
        subst m
        have hstop0 : k+j+5=4*(j+3) := by
          simpa using hstop
        exact high_stop_mzero_18791 j k hj hstop0 hr
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms blank_halts_iff_six_mzero_sumzero_s293
end BB6.Agent11M0SumZeroS293Full
