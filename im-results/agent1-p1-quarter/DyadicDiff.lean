import RootWallArithmetic

namespace BB6.Agent1OneReset

/-- If two naturals differ by a positive K smaller than 2^p, the larger
    is divisible by 2^p, and the smaller by 2^n, then n<p and 2^n<=K. -/
theorem dyadic_small_difference
  (n p B K R:Nat)
  (hK:0<K) (hsmall:K<2^p)
  (hsum:B+K=R)
  (hR:2^p∣R)
  (hB:2^n∣B) : n<p ∧ 2^n≤K := by
  have key (j:Nat) (hjB:2^j∣B) (hjR:2^j∣R) : 2^j∣K := by
    have hsumdiv:2^j∣B+K := by rw [hsum]; exact hjR
    exact (Nat.dvd_add_iff_right hjB).mpr hsumdiv
  by_cases hn:p≤n
  · have hdB:2^p∣B := Nat.dvd_trans (Nat.pow_dvd_pow 2 hn) hB
    have hdK := key p hdB hR
    have hl := Nat.le_of_dvd hK hdK
    omega
  · have hnp:n<p := by omega
    have hdR:2^n∣R := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hR
    have hdK := key n hB hdR
    exact ⟨hnp,Nat.le_of_dvd hK hdK⟩

#print axioms dyadic_small_difference
end BB6.Agent1OneReset
