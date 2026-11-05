import HighInverseSumOne
import JointAllRoot
import LowOneModFour
import HighSumTwo
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Joint

def lowAllowed (m : Nat) : Prop :=
  BB6.Agent3.jointLowAllowed m ∧ m%4≠1

def highAllowed (j m : Nat) : Prop :=
  BB6.Agent19Joint.highAllowed j m ∧ (j+m)%4≠0 ∧
  ¬(2≤m ∧ (j+m)%16=6 ∧ m%4≠1)

private theorem low_bound (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+3=(2*m+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

private theorem high_margin (m : Nat) :
    3*m+12 ≤ 3*2^(2*m+2) := by
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

/-- Lossless source-exact Machine C blank-halting criterion after
    excluding the low m=1 mod4 family, high (j+m)=0 mod4, and the
    two-step high (j+m)=6 mod16, m mod4 != 1 family. The unbounded
    existential parameters remain unresolved. -/
theorem blank_halts_iff_joint_image :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowed m ∧
        BB6.Agent3.mixedFastRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent3.mixedFastRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent19Joint.blank_halts_iff_combined_parametric]
  constructor
  · rintro (⟨m,hlow,hroot⟩ | ⟨j,m,hhigh,hroot⟩)
    · have hnon : m%4≠1 := by
        intro hm
        let k := 2^(2*m+3)-(3*m+4)
        have hr := (BB6.Agent3.mixedFastRootDecision_iff 1 k).mp hroot
        have hstop : k+3*m+4=2^(2*m+3) := by
          dsimp [k]
          have hc := Nat.sub_add_cancel (low_bound m)
          omega
        exact (BB6.Agent11Low.blank_no_low_m_one_mod_four m k hm hstop).2 hr
      exact Or.inl ⟨m,⟨hlow,hnon⟩,hroot⟩
    · have hnon : (j+m)%4≠0 := by
        intro hjm
        let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
        have hr := (BB6.Agent3.mixedFastRootDecision_iff (2*j+3) k).mp hroot
        have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
          dsimp [k]
          have hc := Nat.sub_add_cancel (high_bound j m)
          omega
        exact (BB6.Agent11High.blank_no_high_jplusm_zero_modfour j m k hjm hstop).2 hr
      have hnon2 : ¬(2≤m ∧ (j+m)%16=6 ∧ m%4≠1) := by
        rintro ⟨hm,hjm,hm4⟩
        let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
        have hr := (BB6.Agent3.mixedFastRootDecision_iff (2*j+3) k).mp hroot
        have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
          dsimp [k]
          have hc := Nat.sub_add_cancel (high_bound j m)
          omega
        exact (BB6.Agent11High.blank_no_high_jplusm_six_mod16 j m k hm hjm hm4 hstop) hr
      exact Or.inr ⟨j,m,⟨hhigh,hnon,hnon2⟩,hroot⟩
  · rintro (⟨m,⟨hlow,_⟩,hroot⟩ | ⟨j,m,⟨hhigh,_,_⟩,hroot⟩)
    · exact Or.inl ⟨m,hlow,hroot⟩
    · exact Or.inr ⟨j,m,hhigh,hroot⟩

#print axioms blank_halts_iff_joint_image
end BB6.Agent11Joint
