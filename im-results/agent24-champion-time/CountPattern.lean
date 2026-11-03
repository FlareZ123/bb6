import Lean.Elab.Tactic.Omega

namespace BB6ChampionArithmetic

/-- Valuations of consecutive positive integers from 1 to 2^b - 1. -/
def carryPattern : Nat → List Nat
  | 0 => []
  | b+1 => carryPattern b ++ [b] ++ carryPattern b

theorem carryPattern_length (b : Nat) : (carryPattern b).length + 1 = 2^b := by
  induction b with
  | zero => decide
  | succ b ih =>
    simp only [carryPattern, List.length_append, List.length_cons, List.length_nil]
    rw [Nat.pow_succ]
    omega

theorem carryPattern_sum (b : Nat) : (carryPattern b).sum + b + 1 = 2^b := by
  induction b with
  | zero => decide
  | succ b ih =>
    simp only [carryPattern, List.sum_append, List.sum_cons, List.sum_nil,
      Nat.add_zero]
    rw [Nat.pow_succ]
    omega

/-- Cost of a stream of binary decrements with successive right counters. -/
def charge : List Nat → Nat → Nat
  | [], _ => 0
  | v::rest, c => 48 + 12*v + 12*c + charge rest (c+1)

theorem charge_append (xs ys : List Nat) (c : Nat) :
    charge (xs++ys) c = charge xs c + charge ys (c+xs.length) := by
  induction xs generalizing c with
  | nil => simp [charge]
  | cons x xs ih =>
    simp only [List.cons_append, charge, List.length_cons]
    rw [ih]
    have hh : c + (xs.length+1) = (c+1)+xs.length := by omega
    rw [hh]
    omega

theorem charge_shift (xs : List Nat) (c : Nat) :
    charge xs c = charge xs 0 + 12*c*xs.length := by
  induction xs generalizing c with
  | nil => simp [charge]
  | cons x xs ih =>
    simp only [charge, List.length_cons]
    rw [ih (c+1), ih 1]
    have z : 12*c*(xs.length+1) = 12*c*xs.length +12*c := by
      rw [Nat.mul_succ]
    rw [z]
    have z2 : 12*(c+1)*xs.length = 12*c*xs.length + 12*xs.length := by
      calc
        12*(c+1)*xs.length = (12*c+12)*xs.length := by rw [Nat.mul_succ]
        _ = 12*c*xs.length + 12*xs.length := by rw [Nat.add_mul]
    rw [z2]
    omega

def drainPattern (b : Nat) : Nat := charge (carryPattern b) 0

theorem drainPattern_step (b : Nat) :
  drainPattern (b+1) =
  2*drainPattern b + 48 + 12*b + 12*(carryPattern b).length +
  12*(carryPattern b).length * ((carryPattern b).length+1) := by
  simp only [drainPattern, carryPattern]
  rw [charge_append, charge_append]
  simp only [charge, List.length_singleton, Nat.zero_add, List.length_append]
  rw [charge_shift (carryPattern b) ((carryPattern b).length+1)]
  have z : 12 * ((carryPattern b).length+1) * (carryPattern b).length =
    12 * (carryPattern b).length * ((carryPattern b).length+1) := by
      rw [Nat.mul_assoc, Nat.mul_comm ((carryPattern b).length+1), ← Nat.mul_assoc]
  rw [z]
  omega

theorem pow4_eq_pow2_mul (b : Nat) : 4^b = (2^b)*(2^b) := by
  change (2*2)^b = 2^b*2^b
  exact Nat.mul_pow 2 2 b

theorem drainPattern_step_simple (b : Nat) :
    drainPattern (b+1) = 2*drainPattern b +12*4^b+12*b+36 := by
  let N := (carryPattern b).length
  have hlen : N+1 = 2^b := carryPattern_length b
  have hsq : 12*N+12*N*(N+1)+12 = 12*(N+1)*(N+1) := by
    simp only [Nat.mul_succ, Nat.succ_mul]
    omega
  rw [drainPattern_step]
  change 2*drainPattern b +48+12*b+12*N+12*N*(N+1) = _
  calc
    2*drainPattern b +48+12*b+12*N+12*N*(N+1) =
        2*drainPattern b +12*b+36 + (12*N+12*N*(N+1)+12) := by omega
    _ = 2*drainPattern b +12*b+36 +12*(N+1)*(N+1) := by rw [hsq]
    _ = 2*drainPattern b +12*b+36 +12*4^b := by rw [hlen, pow4_eq_pow2_mul, Nat.mul_assoc]
    _ = 2*drainPattern b +12*4^b+12*b+36 := by omega

/-- Exact closed sum of the proposed LC decrement costs, provable in Lean.
    The statement does NOT claim the raw Turing-machine micro-cost rule. -/
theorem drainPattern_closed (b : Nat) :
    drainPattern b +12*b+48 = 6*4^b+42*2^b := by
  induction b with
  | zero => decide
  | succ b ih =>
    rw [drainPattern_step_simple, Nat.pow_succ, Nat.pow_succ]
    omega

#print axioms carryPattern_length
#print axioms carryPattern_sum
#print axioms drainPattern_closed

end BB6ChampionArithmetic
