import Lean

/-!
# TM63 tower arithmetic corrections

This file isolates the elementary tetration arithmetic used by the
TM63 champion-score sandwich.  T n denotes 2 ↑↑ n, with T 0 = 1.

The key correction is that from
M + N + 50 < T (M + 49) and M + 49 < T 11 - 1
one obtains M + N + 50 < T (T 11 - 1), hence
b < T (T (T 11 - 1)) after applying the V-index upper bound.
The stronger score endpoint is then T (T (T 11 - 1) + 1).

The file treats the preceding TM63 source/cost estimates as hypotheses.
It does not certify the underlying machine-run composition.
-/

open Nat

def T : Nat → Nat
  | 0 => 1
  | n + 1 => 2 ^ T n

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

theorem T_ge_four {n : Nat} (h : 2 ≤ n) : 4 ≤ T n := by
  have hm := T_mono h
  simpa [T] using hm

theorem two_mul_lt_two_pow : ∀ n : Nat, 4 ≤ n → 2 * n < 2 ^ n := by
  intro n
  induction n with
  | zero =>
      intro h
      omega
  | succ n ih =>
      intro h
      by_cases hn : n = 3
      · subst n
        decide
      · have hn4 : 4 ≤ n := by omega
        have hih := ih hn4
        have hpow : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega : n ≠ 0) 2
        calc
          2 * (n + 1) = 2 * n + 2 := by omega
          _ < 2 ^ n + 2 ^ n := by omega
          _ = 2 ^ (n + 1) := by
            rw [Nat.pow_succ]
            omega

/-- The corrected index lift: no tetration level is dropped. -/
theorem corrected_index_bound
    (M N : Nat)
    (hN : N < T (M + 48))
    (hM : M + 50 < T (M + 48))
    (hI : M + 49 < T 11 - 1) :
    M + N + 50 < T (T 11 - 1) := by
  have hT4 : 4 ≤ T (M + 48) := T_ge_four (by omega)
  have hdouble : 2 * T (M + 48) < 2 ^ T (M + 48) :=
    two_mul_lt_two_pow (T (M + 48)) hT4
  have hsum : M + N + 50 < 2 * T (M + 48) := by omega
  have hstep : M + N + 50 < T (M + 49) := by
    calc
      M + N + 50 < 2 * T (M + 48) := hsum
      _ < 2 ^ T (M + 48) := hdouble
      _ = T (M + 49) := by rfl
  have hmono : T (M + 49) ≤ T (T 11 - 1) :=
    T_mono (Nat.le_of_lt hI)
  exact Nat.lt_of_lt_of_le hstep hmono

/-- Corrected form of the b_N upper estimate. -/
theorem corrected_bN_bound
    (M N b : Nat)
    (hN : N < T (M + 48))
    (hM : M + 50 < T (M + 48))
    (hI : M + 49 < T 11 - 1)
    (hb : b < T (M + N + 50)) :
    b < T (T (T 11 - 1)) := by
  have hi := corrected_index_bound M N hN hM hI
  have hm := T_mono (Nat.le_of_lt hi)
  exact Nat.lt_of_lt_of_le hb hm

theorem corrected_score_upper
    (S b X : Nat)
    (hS : S < 9 * b ^ 2)
    (hb : b < T X)
    (hpoly : 12 * (T X) ^ 2 < 2 ^ (T X)) :
    S < T (X + 1) := by
  have hb_le : b ≤ T X := Nat.le_of_lt hb
  have hsquare : b ^ 2 ≤ (T X) ^ 2 := Nat.pow_le_pow_left hb_le 2
  have h9 : 9 * b ^ 2 ≤ 9 * (T X) ^ 2 :=
    Nat.mul_le_mul_left 9 hsquare
  have h12 : 9 * (T X) ^ 2 < 12 * (T X) ^ 2 := by
    have hpos : 0 < (T X) ^ 2 := Nat.pow_pos (T_pos X)
    omega
  have hfinal : S < 2 ^ (T X) :=
    Nat.lt_trans hS (Nat.lt_of_le_of_lt h9 (Nat.lt_trans h12 hpoly))
  simpa [T] using hfinal

theorem square_succ_le_two_sq (n : Nat) (hn : 3 ≤ n) :
    (n + 1) ^ 2 ≤ 2 * n ^ 2 := by
  have hpowN : n ^ 2 = n * n := by
    rw [Nat.pow_succ]
    simp
  have hpowS : (n + 1) ^ 2 = (n + 1) * (n + 1) := by
    rw [Nat.pow_succ]
    simp
  have h2 : 1 ≤ n - 2 := by omega
  have hprod : n ≤ n * (n - 2) := by
    simpa using (Nat.mul_le_mul_left n h2)
  have hdecomp : n ^ 2 = n * (n - 2) + 2 * n := by
    rw [hpowN]
    calc
      n * n = n * ((n - 2) + 2) := by congr 1 <;> omega
      _ = n * (n - 2) + n * 2 := by rw [Nat.mul_add]
      _ = n * (n - 2) + 2 * n := by omega
  have hexp : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by
    rw [hpowS, hpowN]
    calc
      (n + 1) * (n + 1) = n * (n + 1) + (n + 1) := by
        rw [Nat.add_mul]
        simp
      _ = n * n + n + n + 1 := by
        rw [Nat.mul_add]
        omega
      _ = n * n + 2 * n + 1 := by omega
  have hprod1 : 1 ≤ n * (n - 2) := by omega
  omega

theorem twelve_sq_lt_pow2 : ∀ n : Nat, 64 ≤ n → 12 * n ^ 2 < 2 ^ n := by
  intro n
  induction n with
  | zero =>
      intro h
      omega
  | succ n ih =>
      intro h
      by_cases hn : n = 63
      · subst n
        decide
      · have hn64 : 64 ≤ n := by omega
        have hih := ih hn64
        have hsq : (n + 1) ^ 2 ≤ 2 * n ^ 2 :=
          square_succ_le_two_sq n (by omega)
        have hmul : 12 * (2 * n ^ 2) < 2 * 2 ^ n := by omega
        calc
          12 * (n + 1) ^ 2 ≤ 12 * (2 * n ^ 2) :=
            Nat.mul_le_mul_left 12 hsq
          _ < 2 * 2 ^ n := hmul
          _ = 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega

theorem T_ge64 {n : Nat} (h : 4 ≤ n) : 64 ≤ T n := by
  have hm := T_mono h
  have hbase : 64 ≤ T 4 := by decide
  exact Nat.le_trans hbase hm

theorem corrected_score_upper_no_extra_hyp
    (S b X : Nat)
    (hX : 4 ≤ X)
    (hS : S < 9 * b ^ 2)
    (hb : b < T X) :
    S < T (X + 1) := by
  have hbig : 12 * (T X) ^ 2 < 2 ^ (T X) :=
    twelve_sq_lt_pow2 (T X) (T_ge64 hX)
  exact corrected_score_upper S b X hS hb hbig

/-- The sharpened score upper bound, conditional on the TM63 estimates. -/
theorem full_sharpened_upper
    (S M N b : Nat)
    (hN : N < T (M + 48))
    (hM : M + 50 < T (M + 48))
    (hI : M + 49 < T 11 - 1)
    (hb : b < T (M + N + 50))
    (hS : S < 9 * b ^ 2) :
    S < T (T (T 11 - 1) + 1) := by
  have hX : 4 ≤ T (T 11 - 1) := T_ge_four (by omega)
  have hbY : b < T (T (T 11 - 1)) :=
    corrected_bN_bound M N b hN hM hI hb
  have hscore := corrected_score_upper_no_extra_hyp S b (T (T 11 - 1)) hX hS hbY
  exact hscore

theorem T_succ_gt_of_ge2 {n : Nat} (hn : 2 ≤ n) : T n < T (n + 1) := by
  change T n < 2 ^ T n
  have hT4 : 4 ≤ T n := T_ge_four hn
  have hdouble := two_mul_lt_two_pow (T n) hT4
  omega

/-- The lower-side argument only needs A to dominate B=V_(M+42);
    it must not use B1=V_(M+43), which is much larger than A. -/
theorem corrected_lower_A
    (A B M H : Nat)
    (hH : 2 ≤ H)
    (hM : H < M)
    (hB : T (M + 45) + 1 ≤ B)
    (hA : B ≤ A) :
    T H < A := by
  have hstep : T H < T (H + 1) := T_succ_gt_of_ge2 hH
  have hidx : H + 1 ≤ M + 45 := by omega
  have hmono : T (H + 1) ≤ T (M + 45) := T_mono hidx
  have hTB : T (M + 45) < B := by omega
  have hTA : T (H + 1) < A :=
    Nat.lt_of_le_of_lt hmono (Nat.lt_of_lt_of_le hTB hA)
  exact Nat.lt_trans hstep hTA

#print axioms full_sharpened_upper
#print axioms corrected_lower_A
