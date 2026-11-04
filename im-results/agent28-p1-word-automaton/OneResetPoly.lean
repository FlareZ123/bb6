import OddWordCost
import OneResetGrowth

namespace BB6.Agent28

/-- A wall word cannot have polynomially bounded dyadic length. The proof
    combines the all-depth source-independent cost lower bound with the
    exact quartic gap certified separately in OneResetGrowth. -/
theorem polynomial_cost_incompatible_with_wall (n m : Nat)
    (hn : 30 ≤ n)
    (hpow : 2^m ≤ 24*(n+2)^3)
    (hwall : 2^(n-m) < n) : False := by
  let x := n+2
  have hbig : 24*x^3*(24*x+3) < 7*2^n := by
    simpa only [x] using quartic_growth n hn
  have hx : x=n+2 := rfl
  have hfactor7 : 7 ≤ 24*x+3 := by omega
  have hfactorN : 7*n ≤ 24*x+3 := by omega
  have hsmall : 24*x^3 < 2^n := by
    have hle : 7*(24*x^3) ≤ 24*x^3*(24*x+3) := by
      have hh := Nat.mul_le_mul_left (24*x^3) hfactor7
      simpa only [Nat.mul_comm 7 (24*x^3)] using hh
    have hlt : 7*(24*x^3) < 7*2^n := Nat.lt_of_le_of_lt hle hbig
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hpn : 24*x^3*n < 2^n := by
    have hle : 7*(24*x^3*n) ≤ 24*x^3*(24*x+3) := by
      have hh := Nat.mul_le_mul_left (24*x^3) hfactorN
      calc
        _ = (24*x^3)*(7*n) := by ac_rfl
        _ ≤ (24*x^3)*(24*x+3) := hh
    have hlt : 7*(24*x^3*n) < 7*2^n := Nat.lt_of_le_of_lt hle hbig
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hpowm : 2^m ≤ 24*x^3 := hpow
  have hm : m < n := by
    by_cases h : m < n
    · exact h
    have hnle : n ≤ m := by omega
    have hp : 2^n ≤ 2^m := Nat.pow_le_pow_right (by decide) hnle
    omega
  have hidx : n = m+(n-m) := by omega
  have hpoweq : 2^n = 2^m*2^(n-m) := by
    calc
      _ = 2^(m+(n-m)) := congrArg (fun e:Nat => 2^e) hidx
      _ = 2^m*2^(n-m) := Nat.pow_add 2 m (n-m)
  have hlen : 2^(n-m) ≤ n := by omega
  have hmul : (2^m)*2^(n-m) ≤ (2^m)*n := Nat.mul_le_mul_left (2^m) hlen
  have hmul2 : (2^m)*n ≤ (24*x^3)*n := Nat.mul_le_mul_right n hpowm
  omega

#print axioms BB6.Agent28.polynomial_cost_incompatible_with_wall
end BB6.Agent28
