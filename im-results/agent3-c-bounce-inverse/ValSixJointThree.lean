import ValSixJoint
import ValSixThirdHighSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3ValSix

/-- The source-exact high stopping parameter residual after all three
new, disjoint valuation-six blank-root obstructions. -/
def highAllowedValSixThree (j m : Nat) : Prop :=
  highAllowedValSix j m ∧
  ¬(4≤m ∧ j%32=1 ∧ (j+63)%256=(3*m)%256)

private theorem score_nonnegative_three (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hm : 4*m+4 ≤ 2^(2*m+2) := BB6.Agent29New.power_linear_bound m
  have hp : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  rw [Nat.mul_add]
  omega

/-- The exact original-blank halting iff, now preserving all prior
source-certified restrictions and excluding THREE genuinely new
infinite high-stopping parameter families. The remaining existential
over all naturals is deliberately undecided. -/
theorem blank_halts_iff_joint_val_six_three :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent3.jointLowAllowed m ∧
        BB6.Agent3.mixedFastRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedValSixThree j m ∧
        BB6.Agent3.mixedFastRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [blank_halts_iff_joint_val_six]
  constructor
  · rintro (hlow | ⟨j,m,hallowed,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3.mixedFastRootDecision_iff (2*j+3) k).mp hroot
      have hgate : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (score_nonnegative_three j m)
        omega
      have hnot : ¬(4≤m ∧ j%32=1 ∧ (j+63)%256=(3*m)%256) := by
        rintro ⟨hm,hj,hpair⟩
        exact high_third_cone_blank_unreachable j m k hm hj hpair hgate hr
      exact Or.inr ⟨j,m,⟨hallowed,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hallowed,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hallowed,hroot⟩

#print axioms blank_halts_iff_joint_val_six_three
end BB6.Agent3ValSix
