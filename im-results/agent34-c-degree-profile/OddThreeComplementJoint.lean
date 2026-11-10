import OddThreeWideJoint
import OddThreeComplementSource
import Lean.Elab.Tactic.Omega

/-! An exact genuine-blank Machine C halting criterion with both disjoint
source-certified odd-right strict two/three image obstructions removed. -/
namespace BB6.Agent34OddComplementJoint
open BB6.Agent3ValSix

/-- The previous integrated necessary high-root criterion, strengthened by
both disjoint all-time unreachable original-section parameter classes. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent34OddWideJoint.highAllowed j m ∧
  ¬(4≤m ∧ m%4=0 ∧ 3≤j ∧ j%64=(15*m+62)%64)

private theorem high_score_nonnegative (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hm : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hp : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  rw [Nat.mul_add]
  omega

/-- Every candidate in the complementary source cone fails the exact
authentic blank-root decision, without any run-time or parameter cutoff. -/
theorem forbidden_high_no_root (j m : Nat)
    (hm4 : 4≤m) (hm : m%4=0) (hj3 : 3≤j)
    (hj : j%64=(15*m+62)%64) :
    ¬BB6.Agent3.CReach (2*j+3)
      (2^(2*m+2)*(j+3)-(j+3*m+5)) := by
  intro hr
  let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
  have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
    dsimp [k]
    have hc := Nat.sub_add_cancel (high_score_nonnegative j m)
    omega
  rcases hr with ⟨time,hreach⟩
  exact BB6.Agent34OddComplement.high_stop_blank_unreachable
    j m k time hm4 hm hj3 hj hstop hreach

/-- Lossless exact original-blank halting iff after independent, source
exhaustive strict third-image gates. The existential quantifiers stay open. -/
theorem blank_halts_iff_both_odd :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedValSixFull m ∧
        valSixMixedRootDecision 1 (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent34OddWideJoint.blank_halts_iff_odd_wide]
  constructor
  · rintro (⟨m,hlow,hroot⟩ | ⟨j,m,hhigh,hroot⟩)
    · exact Or.inl ⟨m,hlow,hroot⟩
    · have hnot : ¬(4≤m ∧ m%4=0 ∧ 3≤j ∧
        j%64=(15*m+62)%64) := by
        rintro ⟨hm4,hm,hj3,hj⟩
        have hr : BB6.Agent3.CReach (2*j+3)
            (2^(2*m+2)*(j+3)-(j+3*m+5)) :=
          (BB6.Agent3ValSix.valSixMixedRootDecision_iff
            (2*j+3) (2^(2*m+2)*(j+3)-(j+3*m+5))).mp hroot
        exact forbidden_high_no_root j m hm4 hm hj3 hj hr
      exact Or.inr ⟨j,m,⟨hhigh,hnot⟩,hroot⟩
  · rintro (⟨m,hlow,hroot⟩ | ⟨j,m,⟨hhigh,_⟩,hroot⟩)
    · exact Or.inl ⟨m,hlow,hroot⟩
    · exact Or.inr ⟨j,m,hhigh,hroot⟩

#print axioms forbidden_high_no_root
#print axioms blank_halts_iff_both_odd
end BB6.Agent34OddComplementJoint
