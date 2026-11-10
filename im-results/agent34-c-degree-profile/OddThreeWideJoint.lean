import ValSixJointFull
import OddThreeWideSource
import Lean.Elab.Tactic.Omega

/-! Exact Machine C original-root halting iff with the doubled odd-right
strict third-image gate removed from the high stopping parameters. -/
namespace BB6.Agent34OddWideJoint
open BB6.Agent46
open BB6.Agent3ValSix

/-- Existing exact source-root high sieve, strengthened by the new authentic
blank-root unreachability result; the removed cylinder is infinite. -/
def highAllowed (j m : Nat) : Prop :=
  highAllowedValSixFull j m ∧
    ¬(m%4=3 ∧ j%128=(15*m+2)%128)

private theorem high_score_nonnegative (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hm : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hp : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  rw [Nat.mul_add]
  omega

/-- Previously admitted stopping targets in the new parameter cylinder
are genuinely unreachable on the original blank-derived first-return orbit. -/
theorem forbidden_high_no_root (j m : Nat)
    (hm : m%4=3) (hj : j%128=(15*m+2)%128) :
    ¬BB6.Agent3.CReach (2*j+3)
      (2^(2*m+2)*(j+3)-(j+3*m+5)) := by
  intro hr
  let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
  have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
    dsimp [k]
    have hc := Nat.sub_add_cancel (high_score_nonnegative j m)
    omega
  rcases hr with ⟨time,hreach⟩
  exact BB6.Agent34OddWide.high_stop_blank_unreachable
    j m k time hm hj hstop hreach

/-- Lossless authentically blank-root halting equivalence after integrating
the new source-certified high stopping exclusion. The remaining unbounded
parameter existentials are still open. -/
theorem blank_halts_iff_odd_wide :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedValSixFull m ∧
        valSixMixedRootDecision 1 (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent3ValSix.blank_halts_iff_joint_val_six_full]
  constructor
  · rintro (⟨m,hlow,hroot⟩ | ⟨j,m,hhigh,hroot⟩)
    · exact Or.inl ⟨m,hlow,hroot⟩
    · have hnot : ¬(m%4=3 ∧ j%128=(15*m+2)%128) := by
        rintro ⟨hm,hj⟩
        have hr : BB6.Agent3.CReach (2*j+3)
            (2^(2*m+2)*(j+3)-(j+3*m+5)) :=
          (BB6.Agent3ValSix.valSixMixedRootDecision_iff
            (2*j+3) (2^(2*m+2)*(j+3)-(j+3*m+5))).mp hroot
        exact forbidden_high_no_root j m hm hj hr
      exact Or.inr ⟨j,m,⟨hhigh,hnot⟩,hroot⟩
  · rintro (⟨m,hlow,hroot⟩ | ⟨j,m,⟨hhigh,_⟩,hroot⟩)
    · exact Or.inl ⟨m,hlow,hroot⟩
    · exact Or.inr ⟨j,m,hhigh,hroot⟩

#print axioms forbidden_high_no_root
#print axioms blank_halts_iff_odd_wide
end BB6.Agent34OddWideJoint
