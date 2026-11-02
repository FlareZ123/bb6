import P1InverseLog

namespace BB6.Agent47P1
open BB6.P1Reduction

/-- A nonzero remainder modulo 2^(m+1) gives a source-certified
EXHAUSTIVE inverse enumeration at the fixed depths 0,...,m. -/
theorem inverse_at_depth_le_of_nonzero_mod (b d k c m : Nat)
    (h : GAncestor b d k c)
    (hn : (d+b/2+3)%2^(m+1) ≠ 0) :
    ∃ t ≤ m, inverseAt b d t = some (k,c) := by
  obtain ⟨t,ht,_⟩ := inverseAt_complete b d k c h
  have hp : d+b/2+3 = 2^t*(c+3) := inverseAt_power b d t k c ht
  by_cases hle : t ≤ m
  · exact ⟨t,hle,ht⟩
  have hge : m+1 ≤ t := by omega
  have hdiv : 2^(m+1) ∣ 2^t := Nat.pow_dvd_pow 2 hge
  have hd : 2^(m+1) ∣ d+b/2+3 := by
    rw [hp]
    obtain ⟨z,hz⟩ := hdiv
    refine ⟨z*(c+3), ?_⟩
    rw [hz]
    simp [Nat.mul_assoc]
  exact False.elim (hn (Nat.mod_eq_zero_of_dvd hd))

#print axioms inverse_at_depth_le_of_nonzero_mod
end BB6.Agent47P1
