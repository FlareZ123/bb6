import Std

namespace Agent17SheepPower

private theorem exponential_dominates_linear (n : Nat) :
    3*(n+8)+8 < 7*(2:Nat)^(n+5) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hp : (2:Nat)^(n+1+5) = 2*2^(n+5) := by
        rw [show n+1+5=(n+5)+1 by omega, Nat.pow_succ]
        omega
      have hpos : 0 < (2:Nat)^(n+5) := Nat.two_pow_pos (n+5)
      rw [hp]
      omega

/-- Exact all-exponent exceptional odd-cofactor-three obstruction for a hidden
    Sheep odd block of length one; target exponent j=n+8. -/
theorem no_special_hone (n a : Nat) :
    2^(n+9) ≠ 9*2^a + 3*a + 8 := by
  have hlin := exponential_dominates_linear n
  by_cases h : a ≤ n+5
  · have hpow : (2:Nat)^a ≤ 2^(n+5) :=
      Nat.pow_le_pow_right (by decide) h
    have hp16 : (2:Nat)^(n+9)=16*2^(n+5) := by
      calc
        (2:Nat)^(n+9) = 2^((n+5)+4) := by congr 1
        _ = 2^(n+5)*2^4 := Nat.pow_add 2 (n+5) 4
        _ = 16*2^(n+5) := by simp [Nat.mul_comm]
    rw [hp16]
    omega
  · have hpow : (2:Nat)^(n+6) ≤ 2^a :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hp8 : (2:Nat)^(n+9) = 8*2^(n+6) := by
      calc
        (2:Nat)^(n+9) = 2^((n+6)+3) := by congr 1
        _ = 2^(n+6)*2^3 := Nat.pow_add 2 (n+6) 3
        _ = 8*2^(n+6) := by simp [Nat.mul_comm]
    rw [hp8]
    omega

#print axioms no_special_hone
end Agent17SheepPower
