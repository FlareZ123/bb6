import JointMod128Root
import ValSixHighSource
import ValSixSecondHighSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3ValSix

/-- The exact combined Agent29/Agent19 authentic Machine C high
candidate criterion, further excluding two disjoint new infinite
valuation-six stopping families. -/
def highAllowedValSix (j m : Nat) : Prop :=
  BB6.Agent29Joint.highAllowedPlus j m ∧
  ¬(4≤m ∧ m%8=4 ∧ (j+191)%256=(3*m)%256) ∧
  ¬(4≤m ∧ j%128=81 ∧ (j+63)%256=(3*m)%256)

private theorem score_nonnegative (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hm : 4*m+4 ≤ 2^(2*m+2) := BB6.Agent29New.power_linear_bound m
  have hp : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  rw [Nat.mul_add]
  omega

/-- Genuine blank halting iff one of the original exact low or high
families passes all previous and both new high restrictions AND the
source-certified exact fixed-target root decision. This does not decide
the remaining infinite parameter existential. -/
theorem blank_halts_iff_joint_val_six :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent3.jointLowAllowed m ∧
        BB6.Agent3.mixedFastRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedValSix j m ∧
        BB6.Agent3.mixedFastRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent29Joint.blank_halts_iff_joint_mod128]
  constructor
  · rintro (hlow | ⟨j,m,hallowed,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3.mixedFastRootDecision_iff (2*j+3) k).mp hroot
      have hgate : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (score_nonnegative j m)
        omega
      have h1 : ¬(4≤m ∧ m%8=4 ∧ (j+191)%256=(3*m)%256) := by
        rintro ⟨hm,hm8,hpair⟩
        exact high_val_six_blank_unreachable j m k hm hm8 hpair hgate hr
      have h2 : ¬(4≤m ∧ j%128=81 ∧ (j+63)%256=(3*m)%256) := by
        rintro ⟨hm,hj,hpair⟩
        exact high_second_cone_blank_unreachable j m k hm hj hpair hgate hr
      exact Or.inr ⟨j,m,⟨hallowed,h1,h2⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hallowed,_,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hallowed,hroot⟩

#print axioms blank_halts_iff_joint_val_six
end BB6.Agent3ValSix
