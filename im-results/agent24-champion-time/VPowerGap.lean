import Lean

/-!
# The V power-gap lemma for the TM63 adjacent-tower sandwich

T n = 2 ↑↑ n with T 0 = 1.  V starts at 63 and iterates
V (n+1) = 2^(V n) - 1.

The main result is V j^1040 < T (j+4) for every j ≥ 1.
Combined with 9 V j^2 < V j^1040, this gives the exact
score upper step S < T q when q = j+4 and S < 9 V j^2.

This formalizes the arithmetic power-gap step, not the preceding
TM63 source-run or cost decomposition.
-/

open Nat

def T : Nat → Nat
  | 0 => 1
  | n + 1 => 2 ^ T n

def V : Nat → Nat
  | 0 => 63
  | n + 1 => 2 ^ V n - 1

theorem T_pos (n : Nat) : 0 < T n := by
  induction n with
  | zero => simp [T]
  | succ n ih => simp [T, Nat.pow_pos (by decide : 0 < 2)]

theorem self_le_two_pow (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      calc
        n + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ n + 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by
          rw [Nat.pow_succ]
          omega

theorem T_succ_ge (n : Nat) : T n ≤ T (n + 1) := by
  change T n ≤ 2 ^ T n
  exact self_le_two_pow (T n)

theorem T_mono {a b : Nat} (h : a ≤ b) : T a ≤ T b := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step b h ih =>
      exact Nat.le_trans ih (T_succ_ge b)

theorem V_ge_two (n : Nat) : 2 ≤ V n := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hpow : 4 ≤ 2 ^ V n := by
        simpa using Nat.pow_le_pow_right (by decide : 0 < 2) ih
      simp [V]
      omega

theorem pow_dominates_1040_mul {x : Nat} (hx : 2 ≤ x) :
    1040 * x ≤ x ^ 1040 := by
  have hconst : 1040 ≤ 2 ^ 11 := by decide
  have hbase : 2 ^ 11 ≤ x ^ 11 := Nat.pow_le_pow_left hx 11
  have hexp : x ^ 11 ≤ x ^ 1039 :=
    Nat.pow_le_pow_right (by omega : x > 0) (by omega)
  have h1039 : 1040 ≤ x ^ 1039 :=
    Nat.le_trans hconst (Nat.le_trans hbase hexp)
  have hmul : 1040 * x ≤ x ^ 1039 * x :=
    Nat.mul_le_mul_right x h1039
  have hpow : x ^ 1040 = x ^ 1039 * x := by
    rw [Nat.pow_succ]
  rw [hpow]
  exact hmul

theorem V_power_gap_base : (V 1) ^ 1040 < T 5 := by
  have hV1 : V 1 < 2 ^ 63 := by
    change 2 ^ 63 - 1 < 2 ^ 63
    exact Nat.sub_lt (by decide) (by decide)
  have hpow1 : (V 1) ^ 1040 < (2 ^ 63) ^ 1040 :=
    Nat.pow_lt_pow_left hV1 (by decide)
  have hpowEq : (2 ^ 63) ^ 1040 = 2 ^ (63 * 1040) := by
    exact (Nat.pow_mul 2 63 1040).symm
  have hExp : 63 * 1040 < 65536 := by decide
  have hpow2 : 2 ^ (63 * 1040) < 2 ^ 65536 :=
    Nat.pow_lt_pow_right (by decide : 1 < 2) hExp
  change (V 1) ^ 1040 < 2 ^ 65536
  calc
    (V 1) ^ 1040 < (2 ^ 63) ^ 1040 := hpow1
    _ = 2 ^ (63 * 1040) := hpowEq
    _ < 2 ^ 65536 := hpow2

theorem V_power_gap_succ (j : Nat) :
    (V (j + 1)) ^ 1040 < T (j + 5) := by
  induction j with
  | zero =>
      exact V_power_gap_base
  | succ j ih =>
      change (2 ^ V (j + 1) - 1) ^ 1040 < 2 ^ T (j + 5)
      have hV : 2 ≤ V (j + 1) := V_ge_two (j + 1)
      have hmul : 1040 * V (j + 1) ≤ (V (j + 1)) ^ 1040 :=
        pow_dominates_1040_mul hV
      have hexp : 1040 * V (j + 1) < T (j + 5) :=
        Nat.lt_of_le_of_lt hmul ih
      have hsub : 2 ^ V (j + 1) - 1 < 2 ^ V (j + 1) :=
        Nat.sub_lt (Nat.pow_pos (by decide : 0 < 2)) (by decide)
      have hpow : (2 ^ V (j + 1) - 1) ^ 1040 <
          (2 ^ V (j + 1)) ^ 1040 :=
        Nat.pow_lt_pow_left hsub (by decide)
      have hpowEq : (2 ^ V (j + 1)) ^ 1040 =
          2 ^ (V (j + 1) * 1040) :=
        (Nat.pow_mul 2 (V (j + 1)) 1040).symm
      have hpow' : (2 ^ V (j + 1) - 1) ^ 1040 <
          2 ^ (1040 * V (j + 1)) := by
        have h := Nat.lt_of_lt_of_eq hpow hpowEq
        simpa [Nat.mul_comm] using h
      have hlast : 2 ^ (1040 * V (j + 1)) < 2 ^ T (j + 5) :=
        Nat.pow_lt_pow_right (by decide : 1 < 2) hexp
      exact Nat.lt_trans hpow' hlast

theorem V_power_gap (j : Nat) (hj : 1 ≤ j) :
    (V j) ^ 1040 < T (j + 4) := by
  cases j with
  | zero => omega
  | succ j =>
      simpa using V_power_gap_succ j

theorem ten_mul_square_lt_pow1040 {x : Nat} (hx : 2 ≤ x) :
    9 * x ^ 2 < x ^ 1040 := by
  have hconst : 10 ≤ 2 ^ 4 := by decide
  have hbase : 2 ^ 4 ≤ x ^ 4 := Nat.pow_le_pow_left hx 4
  have hexp : x ^ 4 ≤ x ^ 1038 :=
    Nat.pow_le_pow_right (by omega : x > 0) (by omega)
  have h1038 : 10 ≤ x ^ 1038 :=
    Nat.le_trans hconst (Nat.le_trans hbase hexp)
  have hmul : 10 * x ^ 2 ≤ x ^ 1038 * x ^ 2 :=
    Nat.mul_le_mul_right (x ^ 2) h1038
  have hpow : x ^ 1040 = x ^ 1038 * x ^ 2 := by
    have h := Nat.pow_add x 1038 2
    simpa [Nat.add_comm] using h
  have hstrict : 9 * x ^ 2 < 10 * x ^ 2 := by
    have hpos : 0 < x ^ 2 := Nat.pow_pos (by omega)
    omega
  rw [hpow]
  exact Nat.lt_of_lt_of_le hstrict hmul

theorem score_upper_from_V
    (j b S : Nat)
    (hj : 1 ≤ j)
    (hb : b = V j)
    (hS : S < 9 * b ^ 2) :
    S < T (j + 4) := by
  subst b
  have hV : 2 ≤ V j := V_ge_two j
  have hgap : (V j) ^ 1040 < T (j + 4) := V_power_gap j hj
  have hscore : 9 * (V j) ^ 2 < (V j) ^ 1040 :=
    ten_mul_square_lt_pow1040 hV
  exact Nat.lt_trans (Nat.lt_trans hS hscore) hgap

theorem V_lower (j : Nat) : T (j + 3) + 1 ≤ V j := by
  induction j with
  | zero =>
      decide
  | succ j ih =>
      have hTpos : 0 < T (j + 3) := T_pos (j + 3)
      have h2 : 2 ≤ 2 ^ T (j + 3) :=
        Nat.le_self_pow (by omega : T (j + 3) ≠ 0) 2
      have hstep : T (j + 4) + 1 ≤ 2 ^ (T (j + 3) + 1) - 1 := by
        change 2 ^ T (j + 3) + 1 ≤ 2 ^ (T (j + 3) + 1) - 1
        rw [Nat.pow_succ]
        omega
      have hpow : 2 ^ (T (j + 3) + 1) ≤ 2 ^ V j :=
        Nat.pow_le_pow_right (by decide : 0 < 2) ih
      have hsub : 2 ^ (T (j + 3) + 1) - 1 ≤ 2 ^ V j - 1 :=
        Nat.sub_le_sub_right hpow 1
      change T (j + 4) + 1 ≤ 2 ^ V j - 1
      exact Nat.le_trans hstep hsub

theorem score_dominates_V {b : Nat} (hb : 2 ≤ b) :
    b < 6 * (b + 1) ^ 2 := by
  have hpow : b + 1 ≤ (b + 1) ^ 2 :=
    Nat.le_self_pow (by decide : 2 ≠ 0) (b + 1)
  have h6 : (b + 1) ^ 2 ≤ 6 * (b + 1) ^ 2 := by omega
  omega

theorem score_lower_from_V
    (j b S : Nat)
    (hb : b = V j)
    (hLower : 6 * (b + 1) ^ 2 ≤ S) :
    6 * (T (j + 3) + 2) ^ 2 ≤ S := by
  subst b
  have hVlower : T (j + 3) + 1 ≤ V j := V_lower j
  have hshift : T (j + 3) + 2 ≤ V j + 1 := by omega
  have hsq : (T (j + 3) + 2) ^ 2 ≤ (V j + 1) ^ 2 :=
    Nat.pow_le_pow_left hshift 2
  exact Nat.le_trans (Nat.mul_le_mul_left 6 hsq) hLower

/-- Exact adjacent-tower score bounds from the source/cost inequalities. -/
theorem full_adjacent_tower_score_sandwich
    (j b S : Nat)
    (hj : 1 ≤ j)
    (hb : b = V j)
    (hLower : 6 * (b + 1) ^ 2 ≤ S)
    (hUpper : S < 9 * b ^ 2) :
    6 * (T (j + 3) + 2) ^ 2 ≤ S ∧ S < T (j + 4) := by
  have hlo := score_lower_from_V j b S hb hLower
  have hup := score_upper_from_V j b S hj hb hUpper
  exact ⟨hlo, hup⟩

theorem q_lt_T_J
    (q M J : Nat)
    (hq : q < T (M + 49))
    (hM : M + 49 < J) :
    q < T J := by
  have hmono : T (M + 49) ≤ T J := T_mono (Nat.le_of_lt hM)
  exact Nat.lt_of_lt_of_le hq hmono

/-- If J < T 11, then q < T (T 11), not q < T 11. -/
theorem q_lt_T_T11_of_J
    (q M J : Nat)
    (hq : q < T (M + 49))
    (hM : M + 49 < J)
    (hJ : J < T 11) :
    q < T (T 11) := by
  have hqJ : q < T J := q_lt_T_J q M J hq hM
  have hmono : T J ≤ T (T 11) := T_mono (Nat.le_of_lt hJ)
  exact Nat.lt_of_lt_of_le hqJ hmono

/-- Same adjacent-tower result with the source note's q = j + 4 index. -/
theorem full_adjacent_tower_score_sandwich_at_q
    (j q b S : Nat)
    (hq : q = j + 4)
    (hj : 1 ≤ j)
    (hb : b = V j)
    (hLower : 6 * (b + 1) ^ 2 ≤ S)
    (hUpper : S < 9 * b ^ 2) :
    6 * (T (q - 1) + 2) ^ 2 ≤ S ∧ S < T q := by
  subst q
  simpa using full_adjacent_tower_score_sandwich j b S hj hb hLower hUpper

#print axioms V_power_gap
#print axioms score_upper_from_V
#print axioms full_adjacent_tower_score_sandwich_at_q
