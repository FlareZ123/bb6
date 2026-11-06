import Std

namespace BB6.Agent50SubwallZero

/-- A depth-zero-only root prefix must have a small power-of-two divisor
    whenever its total cost does not exceed the root exponent. -/
theorem zero_arith
    (n m b : Nat) (hm : m ≤ n)
    (hroot : 2^m*(b+12)+2*(n+2)=14*2^n) :
    2^m ≤ 2*(n+2) := by
  have hpn : 2^n = 2^m*2^(n-m) := by
    calc
      2^n = 2^(m+(n-m)) := by congr 1; omega
      _ = 2^m*2^(n-m) := Nat.pow_add 2 m (n-m)
  have hprod : 2^m*(b+12)+2*(n+2) = 2^m*(14*2^(n-m)) := by
    rw [hroot,hpn]
    ac_rfl
  have hpowpos : 0 < (2:Nat)^m := Nat.pow_pos (by decide)
  have hlt : b+12 < 14*2^(n-m) := by
    by_cases hh : b+12 < 14*2^(n-m)
    · exact hh
    have hle : 14*2^(n-m) ≤ b+12 := by omega
    have hmult := Nat.mul_le_mul_left (2^m) hle
    omega
  let k : Nat := 14*2^(n-m)-(b+12)
  have hk : 0<k := by dsimp [k]; omega
  have hfactor : 2^m*k = 2*(n+2) := by
    dsimp [k]
    rw [Nat.mul_sub]
    omega
  have hbound : 2^m ≤ 2^m*k := by
    have hkle : 1 ≤ k := by omega
    have ha : 2^m*1 ≤ 2^m*k := Nat.mul_le_mul_left (2^m) hkle
    simpa using ha
  omega

/-- A numeric lemma used to show that zero-reset cost and the logarithmic
    subwall obstruction cannot simultaneously hold. -/
theorem quadratic_below_power (n : Nat)
    (ho : 13824*(n+2)^8 < 2^n) :
    2*n*(n+2)<2^n := by
  have hbase : n*(n+2) ≤ (n+2)*(n+2) :=
    Nat.mul_le_mul_right (n+2) (by omega)
  have hpow : (n+2)^2 ≤ (n+2)^8 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hbound : 2*n*(n+2) ≤ 13824*(n+2)^8 := by
    calc
      2*n*(n+2)=2*(n*(n+2)) := by ac_rfl
      _ ≤ 2*((n+2)*(n+2)) := Nat.mul_le_mul_left 2 hbase
      _ = 2*(n+2)^2 := by
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one]
        ac_rfl
      _ ≤ 2*(n+2)^8 := Nat.mul_le_mul_left 2 hpow
      _ ≤ 13824*(n+2)^8 := Nat.mul_le_mul_right _ (by decide)
  omega

#print axioms BB6.Agent50SubwallZero.zero_arith
#print axioms BB6.Agent50SubwallZero.quadratic_below_power

end BB6.Agent50SubwallZero
