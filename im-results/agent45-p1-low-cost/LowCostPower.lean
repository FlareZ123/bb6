import Std

namespace BB6.Agent45LowCost

private theorem power16_ge (q : Nat) (hq : 1 ≤ q) :
    64 * (q+1) ≤ 2^(16*q) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r+1 := ⟨q-1, by omega⟩
  have hlinear (r : Nat) : r+1 ≤ 2^(16*r) := by
    induction r with
    | zero => decide
    | succ r ih =>
      have he : 2^(16*(r+1)) = 65536 * 2^(16*r) := by
        rw [show 16*(r+1)=16*r+16 by omega, Nat.pow_add]
        simp only [show (2:Nat)^16=65536 by decide]
        omega
      rw [he]
      omega
  have h := hlinear r
  have he : 2^(16*(r+1)) = 65536 * 2^(16*r) := by
    rw [show 16*(r+1)=16*r+16 by omega, Nat.pow_add]
    simp only [show (2:Nat)^16=65536 by decide]
    omega
  rw [he]
  omega

/-- Algebraic restriction on a blank-compatible power leaf of either exact
    P1 n=16q+2 odd-cone feeder, assuming its inverse mass cost is <=7*2^(16q).
    All inverse equations are inputs; this theorem is not a reachability proof. -/
theorem low_cost_power_leaf_shape
    (q b d m t k c j e : Nat) (hq : 1 ≤ q)
    (he : e = 3 ∨ e = 5)
    (hmass : b+d+2*m+32*q+24 = 56*2^(16*q)+e)
    (hb : 8 ≤ b) (hb4 : b%4=0) (hd : d%2=1) (hc : c%2=0)
    (hinverse : d+b/2+3=2^t*(c+3))
    (ht_bound : t ≤ 16*q+4)
    (hcost : 2*k+c+2*t+1=b+d)
    (hpower : 2*k+8=14*2^j)
    (hsmall : m ≤ 7*2^(16*q)) :
    j=16*q+1 ∧ t=1 ∧
      (e=5 → b=4*m+64*q+12) ∧
      (e=3 → b=4*m+64*q+16) := by
  have hp := power16_ge q hq
  have hbhalf : 2*(b/2)=b := by omega
  have htle : 1 ≤ t := by
    by_cases ht0 : t=0
    · rw [ht0] at hinverse
      simp at hinverse
      omega
    · omega
  have hpow_le : j ≤ 16*q+1 := by
    by_cases h : j ≤ 16*q+1
    · exact h
    have hj2 : 16*q+2 ≤ j := by omega
    have hx : 2^(16*q+2) ≤ 2^j := Nat.pow_le_pow_right (by decide) hj2
    have heq : 2^(16*q+2)=4*2^(16*q) := by
      rw [Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega
    rw [heq] at hx
    rcases he with he|he <;> omega
  have hpow_ge : 16*q+1 ≤ j := by
    by_cases h : 16*q+1 ≤ j
    · exact h
    have hj0 : j ≤ 16*q := by omega
    have hx : 2^j ≤ 2^(16*q) := Nat.pow_le_pow_right (by decide) hj0
    have htwo : 2 ≤ 2^t := by
      have hz : 2^1 ≤ 2^t := Nat.pow_le_pow_right (by decide) htle
      simpa using hz
    have hge : 2*(c+3) ≤ d+b/2+3 := by
      calc
        2*(c+3) ≤ 2^t*(c+3) := Nat.mul_le_mul_right (c+3) htwo
        _ = d+b/2+3 := hinverse.symm
    rcases he with he|he <;> omega
  have hj : j=16*q+1 := by omega
  have hpoweq : 2^j=2*2^(16*q) := by
    rw [hj, Nat.pow_succ]
    omega
  have ht : t=1 := by
    by_cases h : t=1
    · exact h
    have ht2 : 2 ≤ t := by omega
    have hx : 4 ≤ 2^t := by
      simpa using (Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) ht2)
    have hge : 4*(c+3) ≤ d+b/2+3 := by
      calc
        4*(c+3) ≤ 2^t*(c+3) := Nat.mul_le_mul_right (c+3) hx
        _ = d+b/2+3 := hinverse.symm
    rw [hpoweq] at hpower
    rcases he with he|he <;> omega
  have hpoweq' : 2^j=2*2^(16*q) := hpoweq
  rw [ht] at hinverse hcost
  simp only [show (2:Nat)^1=2 by decide] at hinverse
  rw [hpoweq'] at hpower
  refine ⟨hj,ht,?_,?_⟩
  · intro he5
    rw [he5] at hmass
    omega
  · intro he3
    rw [he3] at hmass
    omega

#print axioms BB6.Agent45LowCost.low_cost_power_leaf_shape
end BB6.Agent45LowCost
