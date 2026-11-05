import JointResidual
import MixedFastRoot
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Low-family parameter restrictions established in the source-checked
    joint lossless halting criterion. -/
def jointLowAllowed (m : Nat) : Prop :=
  m%1024≠424 ∧ m%4096≠4008 ∧ m%32768≠30632 ∧
  m%16≠14 ∧ m%64≠38 ∧ m%16384≠5032 ∧ m%8≠4

/-- High-family parameter restrictions from five independent all-time
    root exclusions, all source-checked. -/
def jointHighAllowed (j m : Nat) : Prop :=
  ¬ (2≤m ∧ j%4=3 ∧ (j+3*m+7)%16=0) ∧
  ¬ (2≤m ∧ j%4=1 ∧ (j+3*m+11)%32=0) ∧
  ¬ (4≤m ∧
      ((m%4=0 ∧ (j+m)%32=26) ∨
       (m%4=1 ∧ (j+m)%32=2))) ∧
  ¬ (m=1 ∧ j%32=1) ∧
  ¬ (2≤m ∧ j%2=1 ∧ (j+3*m+5)%8=0)

private theorem low_score_nonnegative (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have hp : 0 < (2:Nat)^(2*m+3) := Nat.pow_pos (by decide)
      have he : 2*(m+1)+3 = (2*m+3)+2 := by omega
      rw [he,Nat.pow_add]
      have hf : (2:Nat)^2=4 := by decide
      rw [hf]
      omega

private theorem high_score_nonnegative (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 1 ≤ (2:Nat)^(2*m+2) := by
    exact Nat.pow_pos (by decide)
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

/-- Complete rooted BB6 Machine C stopping criterion as an arithmetical
    parameter-existence problem, with NO existential run-time variable.
    The Boolean decider is source-equivalent to blank-section reachability
    for each individual pair. This does NOT decide the infinite existence. -/
theorem blank_halts_iff_joint_parametric_decision :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, jointLowAllowed m ∧
         mixedFastRootDecision 1 (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, jointHighAllowed j m ∧
         mixedFastRootDecision (2*j+3)
           (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [blank_halts_iff_joint_low_high_sieve]
  constructor
  · rintro ⟨time,a,k,hr,hgate⟩
    rcases hgate with ⟨ha,m,heq,h1,h2,h3,h4,h5,h6,h7⟩ |
      ⟨j,m,ha,heq,h1,h2,h3,h4,h5⟩
    · have hform : k=2^(2*m+3)-(3*m+4) := by
        have hcancel := Nat.sub_add_cancel (low_score_nonnegative m)
        omega
      subst a
      refine Or.inl ⟨m,⟨h1,h2,h3,h4,h5,h6,h7⟩,?_⟩
      rw [←hform]
      exact (mixedFastRootDecision_iff 1 k).mpr ⟨time,hr⟩
    · have hform : k=2^(2*m+2)*(j+3)-(j+3*m+5) := by
        have hcancel := Nat.sub_add_cancel (high_score_nonnegative j m)
        omega
      subst a
      refine Or.inr ⟨j,m,⟨h1,h2,h3,h4,h5⟩,?_⟩
      rw [←hform]
      exact (mixedFastRootDecision_iff (2*j+3) k).mpr ⟨time,hr⟩
  · rintro (⟨m,hm,hroot⟩ | ⟨j,m,hm,hroot⟩)
    · obtain ⟨time,hr⟩ :=
        (mixedFastRootDecision_iff 1 (2^(2*m+3)-(3*m+4))).mp hroot
      have heq : (2^(2*m+3)-(3*m+4))+3*m+4=2^(2*m+3) := by
        have hcancel := Nat.sub_add_cancel (low_score_nonnegative m)
        omega
      rcases hm with ⟨h1,h2,h3,h4,h5,h6,h7⟩
      exact ⟨time,1,2^(2*m+3)-(3*m+4),hr,
        Or.inl ⟨rfl,m,heq,h1,h2,h3,h4,h5,h6,h7⟩⟩
    · obtain ⟨time,hr⟩ :=
        (mixedFastRootDecision_iff (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))).mp hroot
      have heq : (2^(2*m+2)*(j+3)-(j+3*m+5))+j+3*m+5 =
          2^(2*m+2)*(j+3) := by
        have hcancel := Nat.sub_add_cancel (high_score_nonnegative j m)
        omega
      rcases hm with ⟨h1,h2,h3,h4,h5⟩
      exact ⟨time,2*j+3,2^(2*m+2)*(j+3)-(j+3*m+5),hr,
        Or.inr ⟨j,m,rfl,heq,h1,h2,h3,h4,h5⟩⟩

#print axioms blank_halts_iff_joint_parametric_decision
end BB6.Agent3
