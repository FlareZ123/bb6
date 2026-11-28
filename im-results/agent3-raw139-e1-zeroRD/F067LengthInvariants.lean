import TowerCost

namespace BB6.Agent3F067LengthInvariants

open F067Cost
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
Exact length-only identities for the two auxiliary counters of the
source-pinned F067 tower-cost algebra.

Neither `d` nor `e` depends on the numerical values of the stack digits.
The identities are division-free, so they can serve as induction lemmas
for symbolic bit-length estimates of deeply nested towers without ever
materializing the tower's astronomically large contents.
-/

/-- Exact closed form: d(ks) = (56/15) · (16^|ks| - 1).
    Division is avoided to preserve a linear Nat proof. -/
theorem d_length_exact (ks : List Nat) :
    15 * d ks + 56 = 56 * 16 ^ ks.length := by
  induction ks with
  | nil => decide
  | cons k ks ih =>
    change 15 * (56 + 16 * d ks) + 56 = 56 * 16 ^ (ks.length + 1)
    rw [pow_succ]
    omega

/-- Exact closed form:
    e(ks) = (56·16^|ks| - 130·4^|ks| + 74)/45.
    This is an integer identity, not an approximate cost estimate. -/
theorem e_length_exact (ks : List Nat) :
    45 * e ks + 130 * 4 ^ ks.length =
      56 * 16 ^ ks.length + 74 := by
  induction ks with
  | nil => decide
  | cons k ks ih =>
    have hd := d_length_exact ks
    change 45 * (10 + 4*d ks + 4*e ks) +
      130 * 4 ^ (ks.length + 1) =
      56 * 16 ^ (ks.length + 1) + 74
    simp only [pow_succ]
    omega

/-- A constant-factor bound for d, valid for arbitrary stack contents. -/
theorem d_length_upper (ks : List Nat) :
    d ks ≤ 4 * 16 ^ ks.length := by
  have hx : 0 < 16 ^ ks.length := Nat.pow_pos (by decide)
  have hd := d_length_exact ks
  omega

/-- A constant-factor bound for e, valid for arbitrary stack contents. -/
theorem e_length_upper (ks : List Nat) :
    e ks ≤ 2 * 16 ^ ks.length := by
  have hx : 0 < 4 ^ ks.length := Nat.pow_pos (by decide)
  have he := e_length_exact ks
  omega

/-- Geometric place-value of the F067 stack digits in radix four. -/
def digitWeight : List Nat → Nat
  | [] => 0
  | k :: ks => k + 4 * digitWeight ks

/-- Exact decomposition of the first tower-time accumulator:
    15·g + 1838 = 420·digitWeight + 28·16^length + 2020·4^length.

    Thus all dependence of g on the actual (potentially enormous) digit
    values factors through ONE radix-four integer. No iteration of tower
    operations is needed to calculate or bound the remaining terms. -/
theorem g_decomposition_exact (ks : List Nat) :
    15 * g ks + 1838 =
      420 * digitWeight ks +
      28 * 16 ^ ks.length + 2020 * 4 ^ ks.length := by
  induction ks with
  | nil => decide
  | cons k ks ih =>
    have hd := d_length_exact ks
    change 15 * (28*k + 390 + 4*g ks + 6*d ks) + 1838 =
      420 * (k + 4*digitWeight ks) +
      28 * 16 ^ (ks.length+1) + 2020 * 4 ^ (ks.length+1)
    simp only [pow_succ]
    omega


/-- Sum of the actual digit values, independently of their positions. -/
def digitSum : List Nat → Nat
  | [] => 0
  | k :: ks => k + digitSum ks

/-- Exact decomposition of the second tower-time accumulator, using only
    stack length, digit sum, and radix-four digit place-value.

    2025·h + 8775·digitSum + 89370
      = 18900·digitWeight + 420·16^length
        + 88950·4^length + 30600·length.

    The absence of any nested tower expression is useful for validating
    upper bounds on source-counted F067 executions. -/
theorem h_decomposition_exact (ks : List Nat) :
    2025 * h ks + 8775 * digitSum ks + 89370 =
      18900 * digitWeight ks +
      420 * 16 ^ ks.length + 88950 * 4 ^ ks.length +
      30600 * ks.length := by
  induction ks with
  | nil => decide
  | cons k ks ih =>
    have hg := g_decomposition_exact ks
    have he := e_length_exact ks
    change 2025 * (5*k + 136 + g ks + h ks + e ks) +
      8775 * (k + digitSum ks) + 89370 =
      18900 * (k + 4 * digitWeight ks) +
      420 * 16 ^ (ks.length + 1) +
      88950 * 4 ^ (ks.length + 1) + 30600 * (ks.length + 1)
    simp only [pow_succ]
    omega


#print axioms d_length_exact
#print axioms e_length_exact
#print axioms d_length_upper
#print axioms e_length_upper
#print axioms g_decomposition_exact
#print axioms h_decomposition_exact
end BB6.Agent3F067LengthInvariants
