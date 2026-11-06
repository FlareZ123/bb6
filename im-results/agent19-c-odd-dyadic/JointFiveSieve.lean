import JointImageSieve
import OddSevenHighFourLink
import MixedFiveNormalize
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Five

def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11Joint.highAllowed j m ∧
  ¬ (m%16=10 ∧ (j+3*m+19)%64=0)

private theorem high_margin (m:Nat) : 3*m+5 ≤ 3*2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+2=(2*m+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

private theorem high_bound (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 1≤2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j≤2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  have hm := high_margin m
  rw [Nat.mul_add]
  omega

/-- Genuine blank halting iff remaining low or stronger high stopping gate
    has a true exact, source-authentic Boolean blank-root decision. -/
theorem blank_halts_iff_five_root : BB6.CReachBridge.RunHalts ↔
    (∃ m, BB6.Agent11Joint.lowAllowed m ∧
       mixedFiveFastRootDecision 1 (2^(2*m+3)-(3*m+4))=true) ∨
    (∃ j m, highAllowed j m ∧
       mixedFiveFastRootDecision (2*j+3)
       (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11Joint.blank_halts_iff_joint_image]
  constructor
  · rintro (⟨m,hallowed,hroot⟩ | ⟨j,m,hallowed,hroot⟩)
    · exact Or.inl ⟨m,hallowed,(mixedFiveFastRootDecision_iff _ _).mpr
          ((BB6.Agent3.mixedFastRootDecision_iff _ _).mp hroot)⟩
    · let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3.mixedFastRootDecision_iff _ _).mp hroot
      have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (high_bound j m)
        omega
      have hn : ¬ (m%16=10 ∧ (j+3*m+19)%64=0) := by
        rintro ⟨hm,hpair⟩
        exact BB6.Agent19Four.blank_no_high_fourlink j m k hm hpair hstop hr
      exact Or.inr ⟨j,m,⟨hallowed,hn⟩,
        (mixedFiveFastRootDecision_iff (2*j+3) k).mpr hr⟩
  · rintro (⟨m,hallowed,hroot⟩ | ⟨j,m,⟨hallowed,_⟩,hroot⟩)
    · exact Or.inl ⟨m,hallowed,(BB6.Agent3.mixedFastRootDecision_iff _ _).mpr
          ((mixedFiveFastRootDecision_iff _ _).mp hroot)⟩
    · exact Or.inr ⟨j,m,hallowed,(BB6.Agent3.mixedFastRootDecision_iff _ _).mpr
          ((mixedFiveFastRootDecision_iff _ _).mp hroot)⟩

#print axioms blank_halts_iff_five_root
end BB6.Agent19Five
