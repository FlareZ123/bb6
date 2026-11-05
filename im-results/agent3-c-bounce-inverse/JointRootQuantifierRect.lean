import JointRootQuantifier
import MixedHighRect512
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Parametric residual after the new original-source infinite high
    cylinder m=5 mod32, j=12 mod32 is eliminated. -/
def jointHighRectAllowed (j m : Nat) : Prop :=
  jointHighAllowed j m ∧ ¬(m%32=5 ∧ j%32=12)

private theorem joint_high_nonnegative (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 1 ≤ (2:Nat)^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  have hm : 3*m+5 ≤ 3*2^(2*m+2) := by
    induction m with
    | zero => decide
    | succ m ih =>
        have hpos : 0 < (2:Nat)^(2*m+2) := Nat.pow_pos (by decide)
        have he : 2*(m+1)+2 = (2*m+2)+2 := by omega
        rw [he,Nat.pow_add]
        have hf : (2:Nat)^2=4 := by decide
        rw [hf]
        have hip : 1 ≤ (2:Nat)^(2*m+2) := Nat.pow_pos (by decide)
        have hij : j ≤ 2^(2*m+2)*j := by
          simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hip
        have hi := ih hip hij
        omega
  rw [Nat.mul_add]
  omega

/-- Authentic blank halting iff a source-exact Boolean root decision
    succeeds for one of the now restricted infinite low/high parameters.
    This is NOT a global decision of the infinite existential proposition. -/
theorem blank_halts_iff_joint_rect_parametric :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, jointLowAllowed m ∧
         mixedFastRootDecision 1 (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, jointHighRectAllowed j m ∧
         mixedFastRootDecision (2*j+3)
           (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [blank_halts_iff_joint_parametric_decision]
  constructor
  · rintro (hlow | ⟨j,m,hallowed,hroot⟩)
    · exact Or.inl hlow
    · have hnot : ¬(m%32=5 ∧ j%32=12) := by
        rintro ⟨hm,hj⟩
        obtain ⟨time,hr⟩ :=
          (mixedFastRootDecision_iff (2*j+3)
            (2^(2*m+2)*(j+3)-(j+3*m+5))).mp hroot
        have heq :
            (2^(2*m+2)*(j+3)-(j+3*m+5))+j+3*m+5 =
              2^(2*m+2)*(j+3) := by
          have hc := Nat.sub_add_cancel (joint_high_nonnegative j m)
          omega
        exact (blank_no_high_rect_m5_j12 j m
          (2^(2*m+2)*(j+3)-(j+3*m+5)) hm hj heq).2 ⟨time,hr⟩
      exact Or.inr ⟨j,m,⟨hallowed,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hallowed,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hallowed,hroot⟩

#print axioms blank_halts_iff_joint_rect_parametric
end BB6.Agent3
