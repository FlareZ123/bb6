import C70Integration
import C23High
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20C23

/-- New high residual: genuinely all values of the 1-in-128 parametric
    cylinder are removed, keeping the fixed-target decision exact. -/
def highAllowedC23 (j m : Nat) : Prop :=
  BB6.Agent20C70.highAllowedC70 j m ∧
    ¬(2≤m ∧ j%4=0 ∧ (j+7)%32=(3*m)%32)

private theorem power_bound23 (m : Nat) :
    4*m+4 ≤ 2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+2=(2*m+2)+2 := by omega
      rw [he, Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

private theorem high_bound23 (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 1 ≤ (2:Nat)^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  have hm := power_bound23 m
  have ht := Nat.mul_le_mul_left 3 hm
  rw [Nat.mul_add]
  omega

/-- Exact, stronger high/low original blank halting criterion with the
    new dense sum23/right4 source obstruction and Agent20C70 barriers.
    The unbounded existential remains open. -/
theorem blank_halts_iff_c23 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent20C70.lowAllowedC70 m ∧
         BB6.Agent3ValSix.valSixMixedRootDecision 1
           (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedC23 j m ∧
         BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
           (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent20C70.blank_halts_iff_c70_both]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff _ _).mp hroot
      have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (high_bound23 j m)
        omega
      have hnot : ¬(2≤m ∧ j%4=0 ∧ (j+7)%32=(3*m)%32) := by
        rintro ⟨hm,hj,hpair⟩
        exact (blank_no_high_sum23_right4 j m k hm hj hpair hstop) hr
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms blank_halts_iff_c23
end BB6.Agent20C23
