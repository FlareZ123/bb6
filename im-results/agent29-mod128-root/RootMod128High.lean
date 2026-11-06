import RootMod128Arithmetic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29New

/-- Elementary dyadic exponential bound, valid at every depth. -/
theorem power_linear_bound (m : Nat) : 4*m+4 ≤ 2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have he : 2^(2*(m+1)+2)=4*(2^(2*m+2)) := by
      have h : 2*(m+1)+2=(2*m+2)+2 := by omega
      rw [h,Nat.pow_add]
      omega
    rw [he]
    have hh : 4*(4*m+4) ≤ 4*(2^(2*m+2)) := Nat.mul_le_mul_left 4 ih
    omega

/-- The high stopping Diophantine equation forces the arithmetic inputs
into the new two-link root-excluded Machine C cylinder. -/
theorem high_target_cylinder (j m k : Nat)
    (hm : 4≤m) (hj : j%8=5)
    (hres : (j+31)%128 = (3*m)%128)
    (hgate : k+j+3*m+5 = 2^(2*m+2)*(j+3)) :
    (2*j+3)%16=13 ∧ (2*j+3+k+1)%128=96 ∧ 34≤k := by
  have hpowdiv : 128 ∣ 2^(2*m+2) := by
    change 2^7 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨q,hq⟩ := hpowdiv
  have hdiv : 128 ∣ k+j+3*m+5 := by
    refine ⟨q*(j+3), ?_⟩
    calc
      k+j+3*m+5 = 2^(2*m+2)*(j+3) := hgate
      _ = (128*q)*(j+3) := by rw [hq]
      _ = 128*(q*(j+3)) := by ac_rfl
  have hhmod : (k+j+3*m+5)%128=0 := Nat.mod_eq_zero_of_dvd hdiv
  have hlow : 4*m+4 ≤ 2^(2*m+2) := power_linear_bound m
  have hp1 : 1≤2^(2*m+2) := by omega
  have hmul : j ≤ 2^(2*m+2)*j := by
    have hh := Nat.mul_le_mul_right j hp1
    simpa using hh
  have hdist : 2^(2*m+2)*(j+3)=2^(2*m+2)*j+3*2^(2*m+2) := by
    simp [Nat.mul_add, Nat.mul_comm]
  constructor
  · omega
  constructor
  · omega
  · omega

#print axioms power_linear_bound
#print axioms high_target_cylinder
end BB6.Agent29New
