import JointRootQuantifierRect
import OddSpecialHighLift
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Joint

/-- Combine Agent3's joint low/high original-root sieve, its extra
    source rectangle, the all-exponent dyadic obstruction, and four
    independently source-certified odd-special high families. -/
def highAllowed (j m:Nat) : Prop :=
  BB6.Agent3.jointHighRectAllowed j m ∧
  (∀ n, ¬(n+4≤2*m+2 ∧
    (j+3*m+3)%2^(n+4)=2^(n+2) ∧
    (2*j+3)%8=(if n%2=0 then 7 else 3))) ∧
  ¬ (2≤m ∧ j%8=7 ∧ (j+3*m+15)%64=0) ∧
  ¬ (2≤m ∧ j%8=3 ∧ (j+3*m+47)%64=0) ∧
  ¬ (3≤m ∧ j%8=5 ∧ (j+3*m+27)%128=0) ∧
  ¬ (3≤m ∧ j%8=1 ∧ (j+3*m+91)%128=0)

private theorem score_nonnegative (j m : Nat) :
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

/-- Single Boolean, runtime-free, original Machine C blank stopping
    iff, consuming both independently certified research branches.
    The parameter existential is still infinite and undecided. -/
theorem blank_halts_iff_combined_parametric :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent3.jointLowAllowed m ∧
        BB6.Agent3.mixedFastRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent3.mixedFastRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent3.blank_halts_iff_joint_rect_parametric]
  constructor
  · rintro (hlow | ⟨j,m,hjoint,hroot⟩)
    · exact Or.inl hlow
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      obtain ⟨time,hr⟩ :=
        (BB6.Agent3.mixedFastRootDecision_iff (2*j+3) k).mp hroot
      have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (score_nonnegative j m)
        omega
      have hnd : ∀ n, ¬ (n+4≤2*m+2 ∧
          (j+3*m+3)%2^(n+4)=2^(n+2) ∧
          (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
        intro n
        rintro ⟨hm,hpair,hj⟩
        exact BB6.Agent19Tower.blank_no_high_stop_all_depth
          n j m k hm hpair hj hstop ⟨time,hr⟩
      have h1 : ¬(2≤m ∧ j%8=7 ∧ (j+3*m+15)%64=0) := by
        rintro ⟨hm,hj,hpair⟩
        exact BB6.Agent19Special.blank_no_high_special_a
          j m k hm hj hpair hstop ⟨time,hr⟩
      have h2 : ¬(2≤m ∧ j%8=3 ∧ (j+3*m+47)%64=0) := by
        rintro ⟨hm,hj,hpair⟩
        exact BB6.Agent19Special.blank_no_high_special_b
          j m k hm hj hpair hstop ⟨time,hr⟩
      have h3 : ¬(3≤m ∧ j%8=5 ∧ (j+3*m+27)%128=0) := by
        rintro ⟨hm,hj,hpair⟩
        exact BB6.Agent19Special.blank_no_high_special_lift_a
          j m k hm hj hpair hstop ⟨time,hr⟩
      have h4 : ¬(3≤m ∧ j%8=1 ∧ (j+3*m+91)%128=0) := by
        rintro ⟨hm,hj,hpair⟩
        exact BB6.Agent19Special.blank_no_high_special_lift_b
          j m k hm hj hpair hstop ⟨time,hr⟩
      exact Or.inr ⟨j,m,⟨hjoint,hnd,h1,h2,h3,h4⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hjoint,_,_,_,_,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hjoint,hroot⟩

#print axioms blank_halts_iff_combined_parametric
end BB6.Agent19Joint
