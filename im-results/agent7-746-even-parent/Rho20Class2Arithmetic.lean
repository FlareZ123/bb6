import T0D0ZeroPhaseArithmetic

namespace Agent7Rho20

open Agent7D0

def aParam (n : Nat) : Nat := 38 + 54*n
def kParam (n : Nat) : Nat := 97 * 2^(aParam n - 7) + 48

theorem a_ge_38 (n : Nat) : 38 ≤ aParam n := by
  simp [aParam]

theorem a_sub7 (n : Nat) : aParam n - 7 = 31 + 54*n := by
  simp [aParam]
  omega

/-- 2 has period 162 modulo 243. -/
theorem pow2_mod243_period (m t : Nat) :
    2^(m + 162*t) % 243 = 2^m % 243 := by
  induction t with
  | zero => simp
  | succ t ih =>
      have heq : m + 162*(t+1) = (m + 162*t) + 162 := by omega
      rw [heq, Nat.pow_add, Nat.mul_mod, ih]
      have h162 : 2^162 % 243 = 1 := by decide
      rw [h162]
      simp

/-- On the eventual period-54 orbit modulo 162, 2^(31+54n) is fixed. -/
theorem pow2_mod162_class (n : Nat) :
    2^(31 + 54*n) % 162 = 146 := by
  induction n with
  | zero => decide
  | succ n ih =>
      have heq : 31 + 54*(n+1) = (31 + 54*n) + 54 := by omega
      rw [heq, Nat.pow_add, Nat.mul_mod, ih]

/-- The three residues of 2^(31+54n) modulo 243, indexed by n modulo 3. -/
theorem pow2_mod243_class (n : Nat) :
    2^(31 + 54*n) % 243 =
      if n % 3 = 0 then 65 else if n % 3 = 1 then 227 else 146 := by
  have hn : n = 3*(n/3) + n%3 := by omega
  rw [hn]
  have heq : 31 + 54*(3*(n/3) + n%3) =
      (31 + 54*(n%3)) + 162*(n/3) := by omega
  rw [heq]
  have hperiod := pow2_mod243_period (31 + 54*(n%3)) (n/3)
  rw [hperiod]
  have hcases : n%3 = 0 ∨ n%3 = 1 ∨ n%3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · simp [h0]
  · simp [h1]
  · simp [h2]

theorem k_mod162 (n : Nat) : kParam n % 162 = 116 := by
  unfold kParam
  rw [a_sub7]
  rw [Nat.add_mod, Nat.mul_mod, pow2_mod162_class]

theorem k_mod243 (n : Nat) :
    kParam n % 243 =
      if n%3 = 0 then 35 else if n%3 = 1 then 197 else 116 := by
  unfold kParam
  rw [a_sub7]
  rw [Nat.add_mod, Nat.mul_mod, pow2_mod243_class]
  have hcases : n%3 = 0 ∨ n%3 = 1 ∨ n%3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · simp [h0]
  · simp [h1]
  · simp [h2]

/-- Reducing an exponent modulo 162 is sound for powers of 2 modulo 243. -/
theorem pow2_mod243_reduce (m : Nat) :
    2^m % 243 = 2^(m%162) % 243 := by
  have hdecomp : m%162 + 162*(m/162) = m := by omega
  have h := pow2_mod243_period (m%162) (m/162)
  rw [hdecomp] at h
  exact h

theorem p_mod243 (n : Nat) : 2^(kParam n) % 243 = 175 := by
  rw [pow2_mod243_reduce, k_mod162]

end Agent7Rho20
