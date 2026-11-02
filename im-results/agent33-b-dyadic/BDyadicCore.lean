import Agent18BOneDim

namespace BB6.OneDim

/-- The two affine branches have 2-adic fixed points -8 and -15. -/
theorem G_balance_even (z : Nat) (hz : z % 2 = 0) :
    2 * (G z + 8) = 3 * (z + 8) := by
  simp only [G]
  omega

theorem G_balance_odd (z : Nat) (hz : z % 2 = 1) :
    2 * (G z + 15) = 3 * (z + 15) := by
  simp only [G]
  omega

/-- Exact scalar dyadic covariance of the recursive two-branch map. -/
theorem G_add_even (z q : Nat) : G (z+2*q) = G z + 3*q := by
  simp only [G]
  omega

theorem iterG_dyadic_shift (j k q z : Nat) :
    iterG j (z+q*2^(k+j)) = iterG j z + q*3^j*2^k := by
  induction j generalizing z q with
  | zero => simp [iterG]
  | succ j ih =>
    have hpow : q*2^(k+(j+1)) = 2*(q*2^(k+j)) := by
      have h : k+(j+1) = (k+j)+1 := by omega
      rw [h, Nat.pow_succ]
      ac_rfl
    have hfirst : G (z+q*2^(k+(j+1))) = G z + (3*q)*2^(k+j) := by
      rw [hpow, G_add_even]
      congr 1
      ac_rfl
    change iterG j (G (z+q*2^(k+(j+1)))) =
      iterG j (G z) + q*3^(j+1)*2^k
    rw [hfirst, ih (3*q) (G z)]
    simp only [Nat.pow_succ]
    ac_rfl

theorem iterG_critical_shift (n z : Nat) :
    iterG n (z+2^n) = iterG n z + 3^n := by
  have h := iterG_dyadic_shift n 0 1 z
  simpa using h

#print axioms iterG_dyadic_shift
end BB6.OneDim
