import Lean
import Init.Omega
namespace BB6.Agent9SExp

def nextQ (q : Nat) : Nat :=
  if q % 3 = 0 then 4*(q/3)
  else if q % 3 = 1 then 4*(q/3)-3
  else 4*(q/3)+1

theorem nextQ_lower (q : Nat) (hq : 16 ≤ q) :
    4*q ≤ 3*nextQ q + 13 := by
  unfold nextQ
  by_cases h0 : q % 3 = 0
  · simp only [ite_eq_left h0]
    omega
  · simp only [ite_eq_right h0]
    by_cases h1 : q % 3 = 1
    · simp only [ite_eq_left h1]
      omega
    · simp only [ite_eq_right h1]
      omega

theorem nextQ_preserves (q : Nat) (hq : 16 ≤ q) :
    16 ≤ nextQ q := by
  have hh := nextQ_lower q hq
  omega

def iterQ (q : Nat) : Nat → Nat
  | 0 => q
  | n+1 => nextQ (iterQ q n)

theorem iterQ_ge (q : Nat) (hq : 16 ≤ q) (n : Nat) :
    16 ≤ iterQ q n := by
  induction n with
  | zero => exact hq
  | succ n ih => exact nextQ_preserves _ ih

theorem nextQ_growth (q : Nat) (hq : 16 ≤ q) :
    4*(q-13) ≤ 3*(nextQ q-13) := by
  have hh := nextQ_lower q hq
  have hn := nextQ_preserves q hq
  omega

theorem exponential_growth (q n : Nat) (hq : 16 ≤ q) :
    4^n*(q-13) ≤ 3^n*(iterQ q n-13) := by
  induction n with
  | zero => simp [iterQ]
  | succ n ih =>
    have hlow := nextQ_growth (iterQ q n) (iterQ_ge q hq n)
    calc
      4^(n+1)*(q-13) = 4*(4^n*(q-13)) := by simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 4*(3^n*(iterQ q n-13)) := Nat.mul_le_mul_left _ ih
      _ = 3^n*(4*(iterQ q n-13)) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 3^n*(3*(nextQ (iterQ q n)-13)) := Nat.mul_le_mul_left _ hlow
      _ = 3^(n+1)*(iterQ q (n+1)-13) := by
        simp [iterQ, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem nextQ_upper (q : Nat) (hq : 16 ≤ q) :
    3 * nextQ q ≤ 4 * q := by
  unfold nextQ
  by_cases h0 : q % 3 = 0
  · simp only [ite_eq_left h0]
    omega
  · simp only [ite_eq_right h0]
    by_cases h1 : q % 3 = 1
    · simp only [ite_eq_left h1]
      omega
    · simp only [ite_eq_right h1]
      omega

theorem exponential_upper (q n : Nat) (hq : 16 ≤ q) :
    3^n * iterQ q n ≤ 4^n * q := by
  induction n with
  | zero => simp [iterQ]
  | succ n ih =>
    have hs := nextQ_upper (iterQ q n) (iterQ_ge q hq n)
    calc
      3^(n+1)*iterQ q (n+1) = 3^n*(3*nextQ (iterQ q n)) := by
        simp only [iterQ, Nat.pow_succ]; ac_rfl
      _ ≤ 3^n*(4*iterQ q n) := Nat.mul_le_mul_left _ hs
      _ = 4*(3^n*iterQ q n) := by ac_rfl
      _ ≤ 4*(4^n*q) := Nat.mul_le_mul_left _ ih
      _ = 4^(n+1)*q := by simp only [Nat.pow_succ]; ac_rfl

theorem q17_lower (n : Nat) :
    4^n*4 ≤ 3^n*(iterQ 17 n-13) := by
  simpa using exponential_growth 17 n (by omega)

theorem q141_lower (n : Nat) :
    4^n*128 ≤ 3^n*(iterQ 141 n-13) := by
  simpa using exponential_growth 141 n (by omega)

theorem q17_upper (n : Nat) :
    3^n*iterQ 17 n ≤ 4^n*17 :=
  exponential_upper 17 n (by omega)

theorem q141_upper (n : Nat) :
    3^n*iterQ 141 n ≤ 4^n*141 :=
  exponential_upper 141 n (by omega)

#print axioms BB6.Agent9SExp.q17_lower
#print axioms BB6.Agent9SExp.q141_lower
#print axioms BB6.Agent9SExp.exponential_growth
#print axioms BB6.Agent9SExp.exponential_upper
end BB6.Agent9SExp
