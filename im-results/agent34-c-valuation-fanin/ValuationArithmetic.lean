import Lean.Elab.Tactic.Omega

/-- If a power of two divides an odd multiple of 2^v, its exponent is at most v. -/
theorem pow2_odd_factor_le (v h u : Nat)
    (hd : 2^h ∣ 2^v*(2*u+1)) : h ≤ v := by
  by_cases hn : h ≤ v
  · exact hn
  have hle : v+1 ≤ h := by omega
  have hh : 2^(v+1) ∣ 2^v*(2*u+1) :=
    Nat.dvd_trans (Nat.pow_dvd_pow 2 hle) hd
  have hz : 2^(v+1) = 2^v*2 := by rw [Nat.pow_succ]
  rw [hz] at hh
  have hp : 0 < 2^v := Nat.pow_pos (by decide)
  have he := (Nat.mul_dvd_mul_iff_left hp).mp hh
  omega

theorem even_input_depth_val (a n v u : Nat)
    (ha : a%2=0)
    (hsum : 2^n*(2*a+4)=2^v*(2*u+1)) : n+2 ≤ v := by
  have hf : 2*a+4=4*(a/2+1) := by omega
  have heq : 2^n*(2*a+4) = 2^(n+2)*(a/2+1) := by
    rw [hf,Nat.pow_add]
    have hp : (2:Nat)^2=4 := by decide
    rw [hp]
    ac_rfl
  have hd : 2^(n+2) ∣ 2^v*(2*u+1) := by
    rw [← hsum,heq]
    exact Nat.dvd_mul_right _ _
  exact pow2_odd_factor_le v (n+2) u hd

theorem odd_input_depth_val (a n v u : Nat)
    (ha : a%2=1)
    (hsum : 2^n*(2*a+6)=2^v*(2*u+1)) : n+2 ≤ v := by
  have hf : 2*a+6=4*((a+3)/2) := by omega
  have heq : 2^n*(2*a+6) = 2^(n+2)*((a+3)/2) := by
    rw [hf,Nat.pow_add]
    have hp : (2:Nat)^2=4 := by decide
    rw [hp]
    ac_rfl
  have hd : 2^(n+2) ∣ 2^v*(2*u+1) := by
    rw [← hsum,heq]
    exact Nat.dvd_mul_right _ _
  exact pow2_odd_factor_le v (n+2) u hd

theorem even_input_depth_parity (a k x y n : Nat)
    (ha : a%2=0)
    (hc : 2*k+a+7+3*n=x+2*y) : (n+1)%2=x%2 := by omega

theorem odd_input_depth_parity (a k x y n : Nat)
    (ha : a%2=1)
    (hc : 2*k+a+7+3*n=x+2*y) : n%2=x%2 := by omega

#print axioms pow2_odd_factor_le
#print axioms even_input_depth_val
#print axioms odd_input_depth_val
#print axioms even_input_depth_parity
#print axioms odd_input_depth_parity
