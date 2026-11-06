import JointFiveSieve
import LowC26
import C26High
import C26ObliqueHigh
import Lean.Elab.Tactic.Omega

namespace BB6.Agent23C26

def lowAllowed (m : Nat) : Prop :=
  BB6.Agent11Joint.lowAllowed m ∧ m%256≠246

def highForbidden (j m : Nat) : Prop :=
  3≤m ∧ (((j+3*m+5)%32=6 ∧ (7*j+233)%256=(3*m)%256) ∨
          ((j+3*m+5)%32=14 ∧ (7*j+41)%256=(3*m)%256))

def highAllowed (j m : Nat) : Prop :=
  BB6.Agent19Five.highAllowed j m ∧ ¬ highForbidden j m

private theorem low_bound (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+3=(2*m+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

private theorem high_margin_any (m : Nat) :
    3*m+5 ≤ 3*2^(2*m+2) := by
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
  have hm := high_margin_any m
  rw [Nat.mul_add]
  omega

/-- Combined original-source time-free halting iff after adding one
    entire low family and one coupled two-parameter high family exclusion. -/
theorem blank_halts_iff_c26_five_root : BB6.CReachBridge.RunHalts ↔
    (∃ m, lowAllowed m ∧
      BB6.Agent19Five.mixedFiveFastRootDecision 1
        (2^(2*m+3)-(3*m+4))=true) ∨
    (∃ j m, highAllowed j m ∧
      BB6.Agent19Five.mixedFiveFastRootDecision (2*j+3)
        (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent19Five.blank_halts_iff_five_root]
  constructor
  · rintro (⟨m,hlow,hroot⟩ | ⟨j,m,hhigh,hroot⟩)
    · have hn : m%256≠246 := by
        intro hm
        let k := 2^(2*m+3)-(3*m+4)
        have hr : BB6.Agent3.CReach 1 k :=
          (BB6.Agent19Five.mixedFiveFastRootDecision_iff 1 k).mp hroot
        have heq : k+3*m+4=2^(2*m+3) := by
          dsimp [k]
          have hc := Nat.sub_add_cancel (low_bound m)
          omega
        exact blank_no_low_m_246_mod256 m k hm heq hr
      exact Or.inl ⟨m,⟨hlow,hn⟩,hroot⟩
    · have hn : ¬ highForbidden j m := by
        rintro ⟨hm,hpair⟩
        let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
        have hr : BB6.Agent3.CReach (2*j+3) k :=
          (BB6.Agent19Five.mixedFiveFastRootDecision_iff (2*j+3) k).mp hroot
        have heq : k+j+3*m+5=2^(2*m+2)*(j+3) := by
          dsimp [k]
          have hc := Nat.sub_add_cancel (high_bound j m)
          omega
        exact blank_no_high_oblique j m k hm hpair heq hr
      exact Or.inr ⟨j,m,⟨hhigh,hn⟩,hroot⟩
  · rintro (⟨m,⟨hlow,_⟩,hroot⟩ | ⟨j,m,⟨hhigh,_⟩,hroot⟩)
    · exact Or.inl ⟨m,hlow,hroot⟩
    · exact Or.inr ⟨j,m,hhigh,hroot⟩

/-- The earlier single residue rectangle is subsumed by the oblique sector. -/
theorem old_high_sieve_in_new (j m : Nat)
    (hj : j%32=31) (hs : (j+3*m+5)%256=230) :
    highForbidden j m := by
  refine ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩

#print axioms old_high_sieve_in_new
#print axioms blank_halts_iff_c26_five_root
end BB6.Agent23C26
