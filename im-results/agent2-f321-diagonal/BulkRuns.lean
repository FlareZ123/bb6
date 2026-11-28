import DiagonalCoordinates
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321Bulk
open BB6.Agent31F321Density
open BB6.Agent2F321Diagonal

/-- Exactly n consecutive `high` branches of the source counter map. -/
inductive HighRun : Nat → Nat → Nat → Nat → Nat → Prop where
  | nil (a d : Nat) : HighRun 0 a d a d
  | step {n a d A D : Nat} (hg : d + 2 ≤ a)
      (tail : HighRun n (a-d-2) (2*d+3) A D) :
      HighRun (n+1) a d A D

/-- Exactly n consecutive `far` branches of the source counter map. -/
inductive FarRun : Nat → Nat → Nat → Nat → Nat → Prop where
  | nil (a d : Nat) : FarRun 0 a d a d
  | step {n a d A D : Nat} (h1 : a < d) (h2 : 3*a+1 ≤ d)
      (tail : FarRun n (4*a+6) (d-3*a) A D) :
      FarRun (n+1) a d A D

theorem high_run_coordinates {n a d A D : Nat} (hr : HighRun n a d A D) :
    X A D = X a d + n ∧ Y D = 2^n * Y d := by
  induction hr with
  | nil a d => simp
  | @step n a d A D hg tail ih =>
      have hc := high_coordinates a d hg
      constructor
      · omega
      · rw [ih.2, hc.2, Nat.pow_succ]
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- A high-only run reaches the terminal diagonal exactly when its initial
    shifted coordinates satisfy the exponential equality. -/
theorem high_run_terminal_equation {n a d A D : Nat}
    (hr : HighRun n a d A D) (ht : A = D + 1) :
    X a d + n = 2^n * Y d := by
  have hc := high_run_coordinates hr
  have hd := (terminal_iff_diagonal A D).mpr ht
  omega

/-- One far step as a subtraction-free linear identity. -/
theorem far_coordinates_linear (a d : Nat) (h1 : a < d) (h2 : 3*a+1 ≤ d) :
    X (4*a+6) (d-3*a) = X a d + 6 ∧
    Y (d-3*a) + 6 * X a d = 4 * Y d + 12 := by
  unfold X Y
  constructor <;> omega

/-- Kernel-checked arbitrary-length far accelerator in the original
    counters. This is the paper bulk formula from the dossier, now derived
    for arbitrary source-faithful `FarRun` lengths. -/
theorem far_run_formula {n a d A D : Nat} (hr : FarRun n a d A D) :
    A + 2 = (a + 2) * 4^n ∧
    D + (a + 2) * (4^n - 1) = d + 6*n := by
  induction hr with
  | nil a d => simp
  | @step n a d A D h1 h2 tail ih =>
      constructor
      · rw [ih.1, Nat.pow_succ]
        simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
          Nat.mul_comm, Nat.mul_left_comm]
        omega
      · have hpos : 1 ≤ 4^n := Nat.one_le_pow n 4 (by omega)
        have hpow : 4^(n+1) - 1 = 4 * (4^n - 1) + 3 := by
          rw [Nat.pow_succ]
          omega
        have hmul : (a+2) * (4^(n+1)-1) =
            (4*a+8) * (4^n-1) + 3*a + 6 := by
          rw [hpow]
          simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
            Nat.mul_comm, Nat.mul_left_comm]
          omega
        rw [hmul]
        have hi := ih.2
        have heq : 4*a+6+2 = 4*a+8 := by omega
        rw [heq] at hi
        omega

/-- A far-only run that exits directly on the terminal diagonal obeys
    the exact quaternary first-exit equation. -/
theorem far_run_terminal_equation {n a d A D : Nat}
    (hr : FarRun n a d A D) (ht : A = D + 1) :
    X a d + 6*n = 2 * (a+2) * 4^n := by
  have hf := far_run_formula hr
  have hpowpos : 1 ≤ 4^n := Nat.one_le_pow n 4 (by omega)
  have hsplit : (a+2) * 4^n = (a+2) * (4^n-1) + (a+2) := by
    have hp : 4^n = (4^n-1)+1 := by omega
    rw [hp]
    simp [Nat.mul_add]
  have htwice : 2 * (a+2) * 4^n = 2 * ((a+2)*4^n) := by
    simp [Nat.mul_assoc]
  rw [htwice]
  unfold X
  omega

#print axioms high_run_coordinates
#print axioms high_run_terminal_equation
#print axioms far_run_formula
#print axioms far_run_terminal_equation
end BB6.Agent2F321Bulk
