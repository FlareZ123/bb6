import Std

namespace Agent10Rho20Phase143246

def a14 (n : Nat) : Nat := 14 + 54*n
def a32 (n : Nat) : Nat := 32 + 54*n
def a46 (n : Nat) : Nat := 46 + 54*n

def k14 (n : Nat) : Nat := 97 * 2^(7 + 54*n) + 48
def k32 (n : Nat) : Nat := 97 * 2^(25 + 54*n) + 48
def k46 (n : Nat) : Nat := 97 * 2^(39 + 54*n) + 48

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

theorem pow2_mod243_reduce (m : Nat) :
    2^m % 243 = 2^(m%162) % 243 := by
  have hdecomp : m%162 + 162*(m/162) = m := by omega
  have h := pow2_mod243_period (m%162) (m/162)
  rw [hdecomp] at h
  exact h

theorem pow2_mod162_phase14 (n : Nat) :
    2^(7 + 54*n) % 162 = 128 := by
  induction n with
  | zero => decide
  | succ n ih =>
      have heq : 7 + 54*(n+1) = (7 + 54*n) + 54 := by omega
      rw [heq, Nat.pow_add, Nat.mul_mod, ih]
      have h54 : 2^54 % 162 = 82 := by decide
      rw [h54]
      decide

theorem pow2_mod162_phase32 (n : Nat) :
    2^(25 + 54*n) % 162 = 20 := by
  induction n with
  | zero => decide
  | succ n ih =>
      have heq : 25 + 54*(n+1) = (25 + 54*n) + 54 := by omega
      rw [heq, Nat.pow_add, Nat.mul_mod, ih]
      have h54 : 2^54 % 162 = 82 := by decide
      rw [h54]
      decide

theorem pow2_mod162_phase46 (n : Nat) :
    2^(39 + 54*n) % 162 = 116 := by
  induction n with
  | zero => decide
  | succ n ih =>
      have heq : 39 + 54*(n+1) = (39 + 54*n) + 54 := by omega
      rw [heq, Nat.pow_add, Nat.mul_mod, ih]
      have h54 : 2^54 % 162 = 82 := by decide
      rw [h54]
      decide

theorem pow2_mod243_phase14 (n : Nat) :
    2^(7 + 54*n) % 243 =
      if n%3 = 0 then 128 else if n%3 = 1 then 47 else 209 := by
  have hn : n = 3*(n/3) + n%3 := by omega
  rw [hn]
  have heq : 7 + 54*(3*(n/3) + n%3) =
      (7 + 54*(n%3)) + 162*(n/3) := by omega
  rw [heq]
  have hp := pow2_mod243_period (7 + 54*(n%3)) (n/3)
  rw [hp]
  have hc : n%3 = 0 ∨ n%3 = 1 ∨ n%3 = 2 := by omega
  rcases hc with h0 | h1 | h2
  · simp [h0]
    decide
  · simp [h1]
    decide
  · simp [h2]
    decide

theorem pow2_mod243_phase32 (n : Nat) :
    2^(25 + 54*n) % 243 =
      if n%3 = 0 then 20 else if n%3 = 1 then 182 else 101 := by
  have hn : n = 3*(n/3) + n%3 := by omega
  rw [hn]
  have heq : 25 + 54*(3*(n/3) + n%3) =
      (25 + 54*(n%3)) + 162*(n/3) := by omega
  rw [heq]
  have hp := pow2_mod243_period (25 + 54*(n%3)) (n/3)
  rw [hp]
  have hc : n%3 = 0 ∨ n%3 = 1 ∨ n%3 = 2 := by omega
  rcases hc with h0 | h1 | h2
  · simp [h0]
    decide
  · simp [h1]
    decide
  · simp [h2]
    decide

theorem pow2_mod243_phase46 (n : Nat) :
    2^(39 + 54*n) % 243 =
      if n%3 = 0 then 116 else if n%3 = 1 then 35 else 197 := by
  have hn : n = 3*(n/3) + n%3 := by omega
  rw [hn]
  have heq : 39 + 54*(3*(n/3) + n%3) =
      (39 + 54*(n%3)) + 162*(n/3) := by omega
  rw [heq]
  have hp := pow2_mod243_period (39 + 54*(n%3)) (n/3)
  rw [hp]
  have hc : n%3 = 0 ∨ n%3 = 1 ∨ n%3 = 2 := by omega
  rcases hc with h0 | h1 | h2
  · simp [h0]
    decide
  · simp [h1]
    decide
  · simp [h2]
    decide

theorem k14_mod162 (n : Nat) : k14 n % 162 = 152 := by
  unfold k14
  rw [Nat.add_mod, Nat.mul_mod, pow2_mod162_phase14]
  decide

theorem k32_mod162 (n : Nat) : k32 n % 162 = 44 := by
  unfold k32
  rw [Nat.add_mod, Nat.mul_mod, pow2_mod162_phase32]
  decide

theorem k46_mod162 (n : Nat) : k46 n % 162 = 122 := by
  unfold k46
  rw [Nat.add_mod, Nat.mul_mod, pow2_mod162_phase46]
  decide

theorem k14_mod243 (n : Nat) :
    k14 n % 243 =
      if n%3 = 0 then 71 else if n%3 = 1 then 233 else 152 := by
  unfold k14
  rw [Nat.add_mod, Nat.mul_mod, pow2_mod243_phase14]
  split_ifs <;> norm_num

theorem k32_mod243 (n : Nat) :
    k32 n % 243 =
      if n%3 = 0 then 44 else if n%3 = 1 then 206 else 125 := by
  unfold k32
  rw [Nat.add_mod, Nat.mul_mod, pow2_mod243_phase32]
  split_ifs <;> norm_num

theorem k46_mod243 (n : Nat) :
    k46 n % 243 =
      if n%3 = 0 then 122 else if n%3 = 1 then 41 else 203 := by
  unfold k46
  rw [Nat.add_mod, Nat.mul_mod, pow2_mod243_phase46]
  split_ifs <;> norm_num

theorem p14_mod243 (n : Nat) : 2^(k14 n) % 243 = 229 := by
  rw [pow2_mod243_reduce, k14_mod162]
  decide

theorem p32_mod243 (n : Nat) : 2^(k32 n) % 243 = 67 := by
  rw [pow2_mod243_reduce, k32_mod162]
  decide

theorem p46_mod243 (n : Nat) : 2^(k46 n) % 243 = 22 := by
  rw [pow2_mod243_reduce, k46_mod162]
  decide

theorem rho20_phase14 (n : Nat) :
    (k14 n + 6*a14 n) % 54 = 20 := by
  have hk : k14 n % 54 = 44 := by omega
  have ha : a14 n % 54 = 14 := by omega
  omega

theorem rho20_phase32 (n : Nat) :
    (k32 n + 6*a32 n) % 54 = 20 := by
  have hk : k32 n % 54 = 44 := by omega
  have ha : a32 n % 54 = 32 := by omega
  omega

theorem rho20_phase46 (n : Nat) :
    (k46 n + 6*a46 n) % 54 = 20 := by
  have hk : k46 n % 54 = 14 := by omega
  have ha : a46 n % 54 = 46 := by omega
  omega

end Agent10Rho20Phase143246
