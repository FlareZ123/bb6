import CThreeDiagonalM0DeepFull
import M0OddRayValTwo
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0ValTwoFull

/-- Third independent infinite m=0 original-blank high stopping family;
    the full C58, all-depth, diagonal and both earlier m=0 ray exclusions
    remain in force. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11M0DeepFull.highAllowed j m ∧
    ¬(m=0 ∧ j%2048=1031)

private theorem high_bound (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hpow : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
  rw [Nat.mul_add]
  omega

/-- Fully authenticated original-blank Machine C iff with one full
    odd diagonal and three pairwise disjoint infinite high m=0 rays
    deleted from the high stopping candidate parameter domain. -/
theorem blank_halts_iff_late_diagonal_mzero_three :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11M0DeepFull.blank_halts_iff_late_diagonal_mzero_two]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff (2*j+3) k).mp hroot
      have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (high_bound j m)
        omega
      have hnot : ¬(m=0 ∧ j%2048=1031) := by
        rintro ⟨hm,hj⟩
        subst m
        exact (BB6.Agent11M0ValTwo.high_stop_mzero_1031 j k hj hstop) hr
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- An infinite family genuinely admitted by every previous combined
    high parameter restriction, so this is strict progress at the
    unbounded original-blank stopping criterion level. -/
theorem valtwo_ray_strict (q : Nat) :
    BB6.Agent11M0DeepFull.highAllowed (1031+2048*q) 0 ∧
      ¬highAllowed (1031+2048*q) 0 := by
  have hprior :
      BB6.Agent11DiagonalLate.highAllowed (1031+2048*q) 0 :=
    BB6.Agent11M0DeepFull.prior_late_diagonal_admits_mzero_three
      (1031+2048*q) (by omega)
  have hfirst : ¬((0:Nat)=0 ∧ (1031+2048*q)%128=71) := by omega
  have hsecond : ¬((0:Nat)=0 ∧ (1031+2048*q)%2048=1159) := by omega
  have hprev : BB6.Agent11M0DeepFull.highAllowed (1031+2048*q) 0 :=
    ⟨⟨hprior,hfirst⟩,hsecond⟩
  refine ⟨hprev,?_⟩
  intro h
  exact h.2 ⟨rfl,by omega⟩

#print axioms blank_halts_iff_late_diagonal_mzero_three
#print axioms valtwo_ray_strict

end BB6.Agent11M0ValTwoFull
