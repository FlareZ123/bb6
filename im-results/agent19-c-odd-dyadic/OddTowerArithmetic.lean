import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Tower

private theorem pow_two_linear (m:Nat) : 2*m+4≤2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have hh : 2^(2*(m+1)+2)=4*2^(2*m+2) := by
      calc
        2^(2*(m+1)+2)=2^((2*m+2)+2) := by congr 1 <;> omega
        _=2^(2*m+2)*2^2 := Nat.pow_add ..
        _=4*2^(2*m+2) := by omega
    rw [hh]
    omega

/-- Exact arithmetic reduction of a high stopping family into
    the variable-depth nonreachability cylinder at exponent three. -/
theorem high_three_arithmetic (j m k:Nat)
    (hm : 3≤m) (hj : j%4=0)
    (hpair : (j+3*m+3)%32=8)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ∃ u v, 1≤v ∧ 2*j+3=8*u+3 ∧ k=32*v+22 := by
  have hpow : 32 ∣ 2^(2*m+2) := by
    change 2^5 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hprodmod : 32 ∣ 2^(2*m+2)*(j+3) := by
    rcases hpow with ⟨z,hz⟩
    refine ⟨z*(j+3),?_⟩
    rw [hz]
    ac_rfl
  have hmod : (k+j+3*m+5)%32=0 := by
    rw [heq]
    exact Nat.mod_eq_zero_of_dvd hprodmod
  have hkmod : (k+2)%32=24 := by omega
  have hb256 : 256 ≤ 2^(2*m+2) := by
    have hh := Nat.pow_le_pow_right (by decide : 0<2)
      (show 8≤2*m+2 by omega)
    simpa only [show (2:Nat)^8=256 by decide] using hh
  have hblin : 2*m+4 ≤ 2^(2*m+2) := pow_two_linear m
  have hJ : 256*j ≤ 2^(2*m+2)*j :=
    Nat.mul_le_mul_right j hb256
  have hprod : 2^(2*m+2)*(j+3) = 2^(2*m+2)*j+3*2^(2*m+2) := by
    simp [Nat.mul_add,Nat.mul_comm]
  have hkbig : 54≤k := by omega
  refine ⟨j/4,(k+2)/32,?_ ,?_ ,?_⟩ <;> omega

#print axioms high_three_arithmetic
end BB6.Agent19Tower
