import C3
import C51
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent46C384

private theorem pow4_mod3 (m : Nat) : 4^m % 3 = 1 := by
  induction m with
  | zero => decide
  | succ m ih =>
      rw [Nat.pow_succ]
      omega

private theorem high_pow_mod384 (m : Nat) (hm : 3≤m) :
    2^(2*m+2)%384 = 256 := by
  have hp : 2^(2*m+2)=256*4^(m-3) := by
    have he : 2*m+2 = 8+2*(m-3) := by omega
    rw [he,Nat.pow_add]
    have ha : 2^(2*(m-3)) = 4^(m-3) := by
      calc
        2^(2*(m-3)) = (2^2)^(m-3) := Nat.pow_mul 2 2 (m-3)
        _ = 4^(m-3) := by simp
    rw [ha]
  rw [hp]
  have ht := pow4_mod3 (m-3)
  omega

private theorem high_halt_mod384 (j m k : Nat)
    (hm : 3≤m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (k+j+3*m+5)%384 = (256*(j+3))%384 := by
  rw [heq]
  have hp := high_pow_mod384 m hm
  calc
    (2^(2*m+2)*(j+3))%384 = ((j+3)*(2^(2*m+2)))%384 := by rw [Nat.mul_comm]
    _ = ((j+3)*((2^(2*m+2))%384))%384 :=
        (Nat.mul_mod_mod (j+3) (2^(2*m+2)) 384).symm
    _ = ((j+3)*256)%384 := by rw [hp]
    _ = (256*(j+3))%384 := by rw [Nat.mul_comm]

theorem second_high_mixed3_excluded (j m k : Nat)
    (hm : 3≤m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hres : (j%384=191 ∧ m%128=67) ∨ (j%384=383 ∧ m%128=3)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  have hmod := high_halt_mod384 j m k hm heq
  have ha : (2*j+3)%384=1 := by rcases hres with h|h <;> omega
  have hk : k%384=115 := by rcases hres with h|h <;> omega
  intro hr
  have hb : BB6.Agent46C3.bad (2*j+3) k 0 := by
    change BB6.Agent46C3.low (2*j+3) k
    unfold BB6.Agent46C3.low
    exact Or.inl ⟨ha,hk⟩
  exact BB6.Agent46C3.blank_avoids_bad _ hr hb

theorem second_high_mixed51_excluded (j m k : Nat)
    (hm : 3≤m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hres : (j%384=191 ∧ m%128=115) ∨ (j%384=383 ∧ m%128=51)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  have hmod := high_halt_mod384 j m k hm heq
  have ha : (2*j+3)%384=1 := by rcases hres with h|h <;> omega
  have hk : k%384=355 := by rcases hres with h|h <;> omega
  intro hr
  have hb : BB6.Agent46C51.bad (2*j+3) k 0 := by
    change BB6.Agent46C51.low (2*j+3) k
    unfold BB6.Agent46C51.low
    exact Or.inl ⟨ha,hk⟩
  exact BB6.Agent46C51.blank_avoids_bad _ hr hb

#print axioms second_high_mixed3_excluded
#print axioms second_high_mixed51_excluded
end BB6.Agent46C384
