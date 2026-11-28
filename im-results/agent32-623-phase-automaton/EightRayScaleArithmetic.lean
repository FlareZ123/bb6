import Std

namespace BB6.Agent32EightRayScaleArithmetic

/-- A linear depth error is dominated by the exponential scale retained
    after transporting the terminal strip back two ordinary steps. -/
theorem depth_error_le (k : Nat) (hk : 3 ≤ k) :
    16*k+195 ≤ 18*3^k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => decide
  | succ d ih =>
    rw [show 3 + (d+1) = (3+d)+1 by omega, Nat.pow_succ]
    omega

/-- The transported ray index cannot be arbitrarily large on a fixed root. -/
theorem two_step_scale_lower (n m : Nat) (hn : 13 ≤ n)
    (h : 3^(n-1) ≤ 9*m+16*(n+3)+83) : 3^(n-4) ≤ m := by
  have hk : 3 ≤ n-4 := by omega
  have hErr := depth_error_le (n-4) hk
  have he : n-1 = (n-4)+3 := by omega
  rw [he, Nat.pow_add] at h
  simp only [show (3 : Nat)^3 = 27 by decide] at h
  omega

/-- Preserve the third-predecessor lower scale through two source bounds. -/
theorem two_step_scale_transport (n m₀ m₁ m₂ : Nat) (hn : 13 ≤ n)
    (hscale : 3^(n-1) ≤ m₂+3)
    (h01 : m₁ ≤ 3*m₀+4*(n+3)+20)
    (h12 : m₂ ≤ 3*m₁+4*(n+3)+20) : 3^(n-4) ≤ m₀ := by
  apply two_step_scale_lower n m₀ hn
  omega

/-- Any mass-depth upper bound on the transported root bounds the index. -/
theorem ray_index_le_mass_depth (n m S ell : Nat) (hn : 13 ≤ n)
    (hscale : 3^(n-4) ≤ m) (hm : m ≤ S) (hS : S < 3^ell) : n ≤ ell+3 := by
  by_cases h : n ≤ ell+3
  · exact h
  · have hle : ell ≤ n-4 := by omega
    have hp : 3^ell ≤ 3^(n-4) := Nat.pow_le_pow_right (by decide) hle
    omega

#print axioms two_step_scale_transport
#print axioms ray_index_le_mass_depth

end BB6.Agent32EightRayScaleArithmetic
