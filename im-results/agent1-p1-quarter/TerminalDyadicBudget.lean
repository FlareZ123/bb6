import UniversalSmallLeft

namespace BB6.Agent1Bottleneck

/-- Exact dyadic remainder obstruction. With positive D,
D + 2^t(c+3) = 7*2^n implies 2^t ≤ 2D. -/
theorem dyadic_defect_gap (n t c D : Nat)
    (hD : D + 2^t*(c+3) = 7*2^n)
    (hDpos : 0 < D) :
    2^t ≤ 2*D := by
  have hbase : 0 < 2^n := Nat.two_pow_pos n
  by_cases htn : t ≤ n
  · have hdiv : 2^t ∣ 7*2^n := by
      have hd : 2^t ∣ 2^n := Nat.pow_dvd_pow 2 htn
      obtain ⟨z,hz⟩ := hd
      refine ⟨7*z, ?_⟩
      rw [hz]
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    have hs : 2^t ∣ 2^t*(c+3) := ⟨c+3,rfl⟩
    have hsub : 2^t ∣ (7*2^n-2^t*(c+3)) := Nat.dvd_sub hdiv hs
    have hsubeq : 7*2^n - 2^t*(c+3) = D := by omega
    rw [hsubeq] at hsub
    have hle := Nat.le_of_dvd hDpos hsub
    omega
  · have hgt : n+1 ≤ t := by omega
    by_cases heq : t ≤ n+1
    · have ht : t=n+1 := by omega
      subst t
      have hp : 2^(n+1) = 2*2^n := by rw [Nat.pow_succ]; omega
      have hct : c=0 := by
        by_cases hc0 : c=0
        · exact hc0
        have hcz : 1≤c := by omega
        have hmul := Nat.mul_le_mul_left (2^(n+1)) (show 4≤c+3 by omega)
        rw [hp] at hmul
        rw [hp] at hD
        omega
      subst c
      rw [hp] at hD ⊢
      omega
    · have hlarge : n+2 ≤ t := by omega
      have hp : 2^(n+2) ≤ 2^t := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hlarge
      have hpp : 2^(n+2)=4*2^n := by
        rw [Nat.pow_add]
        have hz : (2:Nat)^2=4 := by decide
        rw [hz]
        omega
      have hmul := Nat.mul_le_mul_left (2^t) (show 3≤c+3 by omega)
      omega

#print axioms dyadic_defect_gap
end BB6.Agent1Bottleneck
