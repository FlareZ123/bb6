import Std

namespace Agent44Phase50SixClass

def k6561 (a : Nat) : Nat :=
  (97 * 2 ^ ((a - 7) % 4374) + 48) % 6561

def k4374 (a : Nat) : Nat :=
  (97 * 2 ^ ((a - 7) % 4374) + 48) % 4374

def r4374 (a : Nat) : Nat :=
  (k4374 a + 4 + 4374 - (a % 4374)) % 4374

def p6561 (a : Nat) : Nat :=
  2 ^ (k4374 a) % 6561

def q243 (a : Nat) : Nat :=
  2 ^ ((k4374 a % 162 + 162 - (a % 162)) % 162) % 243

def b6561 (a : Nat) : Nat :=
  ((2 * k6561 a + 7) * (2 ^ (r4374 a) % 6561)) % 6561

def x2187 (a : Nat) : Nat :=
  ((80 * p6561 a + 2 * k6561 a + 13 + 3 * 6561
      - 2 * b6561 a) % 6561) / 3

def x1mod27 (a : Nat) : Nat :=
  (((248 * p6561 a + 20 * 6561 - 8 * b6561 a
      - 10 * k6561 a + 25) % 6561) / 9) % 27

def x2mod81 (a : Nat) : Nat :=
  (16 * (x2187 a / 27) + 10 * 81
      - 4 * (p6561 a % 81) - 2 * (k6561 a % 81) - 1) % 81

def x3mod9 (a : Nat) : Nat :=
  (8 * (x2mod81 a / 9) + 20 * 9
      - (p6561 a % 9) - 2 * (k6561 a % 9) + 3) % 9

def gmod9 (a : Nat) : Nat :=
  ((26368 * (q243 a) + 74 * (k6561 a % 243) + 243 - 23) % 243) / 27

def amod3 (a : Nat) : Nat :=
  (4 * (p6561 a % 3) + 2 * (k6561 a % 3) + 1) % 3

def gprimemod3 (a : Nat) : Nat :=
  (p6561 a % 3 + 2 * (k6561 a % 3) + 81
      - 3 - 4 * (x2mod81 a / 9)) % 3

def row (a : Nat) : List Nat :=
  [x2187 a, x1mod27 a, x2mod81 a, gmod9 a, amod3 a]

theorem pow2_mod6561_period (m t : Nat) :
    2 ^ (m + 4374 * t) % 6561 = 2 ^ m % 6561 := by
  induction t with
  | zero => simp
  | succ t ih =>
      have heq : m + 4374 * (t + 1) = (m + 4374 * t) + 4374 := by omega
      rw [heq, Nat.pow_add, Nat.mul_mod, ih]
      have h4374 : 2 ^ 4374 % 6561 = 1 := by decide
      rw [h4374]
      simp

theorem pow2_mod6561_reduce (m : Nat) :
    2 ^ m % 6561 = 2 ^ (m % 4374) % 6561 := by
  have hdecomp : m % 4374 + 4374 * (m / 4374) = m := by omega
  have h := pow2_mod6561_period (m % 4374) (m / 4374)
  rw [hdecomp] at h
  exact h

theorem pow2_mod6561_1458 : 2 ^ 1458 % 6561 = 2188 := by decide

theorem phase50_representative_rows :
    row 50 = [1296, 21, 60, 1, 0] ∧
    row 536 = [567, 21, 33, 1, 0] ∧
    row 1022 = [2025, 21, 6, 1, 0] ∧
    row 104 = [1701, 21, 57, 1, 0] ∧
    row 590 = [972, 21, 30, 1, 0] ∧
    row 1076 = [243, 21, 3, 1, 0] ∧
    row 212 = [324, 21, 51, 1, 0] ∧
    row 698 = [1782, 21, 24, 1, 0] ∧
    row 1184 = [1053, 21, 78, 1, 0] ∧
    row 320 = [1134, 21, 45, 1, 0] ∧
    row 806 = [405, 21, 18, 1, 0] ∧
    row 1292 = [1863, 21, 72, 1, 0] ∧
    row 374 = [1539, 21, 42, 1, 0] ∧
    row 860 = [810, 21, 15, 1, 0] ∧
    row 1346 = [81, 21, 69, 1, 0] ∧
    row 428 = [1944, 21, 39, 1, 0] ∧
    row 914 = [1215, 21, 12, 1, 0] ∧
    row 1400 = [486, 21, 66, 1, 0] := by
  decide

theorem phase50_class320_branch_residues :
    x3mod9 320 = 5 ∧ gprimemod3 320 = 0 ∧
    x3mod9 806 = 8 ∧ gprimemod3 806 = 0 ∧
    x3mod9 1292 = 2 ∧ gprimemod3 1292 = 0 := by
  decide

theorem phase50_valuation_gates :
    (x2187 50 % 81 = 0 ∧ x2187 50 % 243 ≠ 0) ∧
    (x2187 104 % 243 = 0 ∧ x2187 104 % 729 ≠ 0) ∧
    (x2187 212 % 81 = 0 ∧ x2187 212 % 243 ≠ 0) ∧
    (x2187 320 % 81 = 0 ∧ x2187 320 % 243 ≠ 0) ∧
    (x2187 374 % 81 = 0 ∧ x2187 374 % 243 ≠ 0) ∧
    (x2187 428 % 81 = 0 ∧ x2187 428 % 243 ≠ 0) ∧
    (x2mod81 50 % 3 = 0 ∧ x2mod81 50 % 9 ≠ 0) ∧
    (x2mod81 104 % 3 = 0 ∧ x2mod81 104 % 9 ≠ 0) ∧
    (x2mod81 212 % 3 = 0 ∧ x2mod81 212 % 9 ≠ 0) ∧
    (x2mod81 374 % 3 = 0 ∧ x2mod81 374 % 9 ≠ 0) ∧
    (x2mod81 428 % 3 = 0 ∧ x2mod81 428 % 9 ≠ 0) ∧
    (x2mod81 320 % 9 = 0 ∧ x2mod81 320 % 27 ≠ 0) := by
  decide

end Agent44Phase50SixClass
