import Std

namespace BB6.Agent4Cone

/-- A nonzero residue modulo 2^(m+1) bounds the exponent of every
factorization D = 2^t * (c+3) by m.  This is a general arithmetic
certificate for finite G-ancestor enumeration. -/
theorem inverse_power_depth_bound (D c m : Nat)
    (h : ∃ t : Nat, D = 2^t*(c+3))
    (hn : D%2^(m+1) ≠ 0) :
    ∃ t : Nat, t≤m ∧ D = 2^t*(c+3) := by
  obtain ⟨t,ht⟩ := h
  refine ⟨t,?_,ht⟩
  by_cases hle : t ≤ m
  · exact hle
  have hm : m+1≤t := by omega
  have hp : (2:Nat)^(m+1) ∣ (2:Nat)^t := Nat.pow_dvd_pow 2 hm
  obtain ⟨z,hz⟩ := hp
  have hd : 2^(m+1) ∣ D := by
    rw [ht, hz]
    exact ⟨z*(c+3), by simp [Nat.mul_assoc]⟩
  exact False.elim (hn (Nat.mod_eq_zero_of_dvd hd))

#print axioms BB6.Agent4Cone.inverse_power_depth_bound
end BB6.Agent4Cone
