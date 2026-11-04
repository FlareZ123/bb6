import C38V2
import C58
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent46Mixed192

private theorem pow4_mod3 (m : Nat) : 4^m % 3 = 1 := by
  induction m with
  | zero => decide
  | succ m ih =>
      rw [Nat.pow_succ]
      omega

private theorem high_pow_mod192 (m : Nat) (hm : 2≤m) :
    2^(2*m+2)%192 = 64 := by
  have hp : 2^(2*m+2)=64*4^(m-2) := by
    have he : 2*m+2=6+2*(m-2) := by omega
    rw [he,Nat.pow_add]
    have ha : 2^(2*(m-2))=4^(m-2) := by
      calc
        2^(2*(m-2))=(2^2)^(m-2) := Nat.pow_mul 2 2 (m-2)
        _=4^(m-2) := by simp
    rw [ha]
  rw [hp]
  have ht := pow4_mod3 (m-2)
  omega

private theorem high_halt_mod192 (j m k : Nat)
    (hm : 2≤m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (k+j+3*m+5)%192 = (64*(j+3))%192 := by
  rw [heq]
  have hp := high_pow_mod192 m hm
  calc
    (2^(2*m+2)*(j+3))%192 = ((j+3)*(2^(2*m+2)))%192 := by rw [Nat.mul_comm]
    _ = ((j+3)*((2^(2*m+2))%192))%192 :=
        (Nat.mul_mod_mod (j+3) (2^(2*m+2)) 192).symm
    _ = ((j+3)*64)%192 := by rw [hp]
    _ = (64*(j+3))%192 := by rw [Nat.mul_comm]

/-- Excludes two genuine high-family stopping parameter cylinders
    using the original-source mixed192 C38 backward invariant. -/
theorem second_high_mixed38_excluded (j m k : Nat)
    (hm : 2≤m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hres : (j%192=95 ∧ m%64=6) ∨ (j%192=191 ∧ m%64=38)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  have hmod := high_halt_mod192 j m k hm heq
  have ha : (2*j+3)%192=1 := by rcases hres with h|h <;> omega
  have hk : k%192=10 := by rcases hres with h|h <;> omega
  intro hr
  have hb : BB6.Agent46C38.bad (2*j+3) k 0 := by
    change BB6.Agent46C38.low (2*j+3) k
    unfold BB6.Agent46C38.low
    exact Or.inl ⟨ha,hk⟩
  exact BB6.Agent46C38.blank_avoids_bad _ hr hb

/-- Excludes two further high-family stopping parameter cylinders
    using the original-source mixed192 C58 backward invariant. -/
theorem second_high_mixed58_excluded (j m k : Nat)
    (hm : 2≤m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hres : (j%192=95 ∧ m%64=26) ∨ (j%192=191 ∧ m%64=58)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  have hmod := high_halt_mod192 j m k hm heq
  have ha : (2*j+3)%192=1 := by rcases hres with h|h <;> omega
  have hk : k%192=142 := by rcases hres with h|h <;> omega
  intro hr
  have hb : BB6.Agent46C58.bad (2*j+3) k 0 := by
    change BB6.Agent46C58.low (2*j+3) k
    unfold BB6.Agent46C58.low
    exact Or.inr (Or.inl ⟨ha,hk⟩)
  exact BB6.Agent46C58.blank_avoids_bad _ hr hb

#print axioms second_high_mixed38_excluded
#print axioms second_high_mixed58_excluded
end BB6.Agent46Mixed192
