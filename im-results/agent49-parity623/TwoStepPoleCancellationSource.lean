import Agent49TernaryShiftSource
import Agent8BudgetSource

/-!
A synthetic two-step cancellation family for Cryptids #623.

This is an exact trajectory of the original high-level source map, but it is
not claimed to be reachable from the blank root. It demonstrates that the
projective two-step pole can be approached and even attained after the exact
ternary-drain corrections on states elsewhere in the admissible cone.
-/

namespace BB6.Agent49TwoStepPoleCancellation

open BB6.Agent49ParitySource
open BB6.Agent49TernaryShiftSource
open BB6.Agent8BudgetSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- The input family parameterized by a tight drain block. -/
def xFamily (m : Nat) : Nat := 3 * tightB m + 2

theorem tightB_mod_two (m : Nat) : tightB m % 2 = m % 2 := by
  induction m with
  | zero =>
      simp [tightB]
  | succ m ih =>
      simp only [tightB]
      omega

theorem xFamily_even (m : Nat) (hm : m % 2 = 0) :
    xFamily m % 2 = 0 := by
  simp [xFamily, tightB_mod_two, hm]

/-- Exact base transition for the right-even ray. -/
theorem base_right_even (m : Nat) (hm : m % 2 = 0) :
    highLevelNext (.D (xFamily m) (2 * xFamily m + 2)) =
      some (.D (xFamily m + m + 4) (3 * xFamily m + 3)) := by
  let x := xFamily m
  have hxpos : 0 < x := by
    dsimp [x, xFamily]
    omega
  have hxeven : x % 2 = 0 := by
    simpa [x] using xFamily_even m hm
  have hxmod : x % 3 = 2 := by
    dsimp [x, xFamily]
    omega
  have hxdiv : x / 3 = tightB m := by
    dsimp [x, xFamily]
    omega
  have heval :
      evalA (x + 3) x (2 * x + 5) =
        some (x + 4, tightB m, 2 * x + 5) := by
    simp [evalA, hxmod, hxdiv]
  have hthird : 2 * x + 5 + 3 * tightB m = 3 * x + 3 := by
    dsimp [x, xFamily]
    omega
  have hdrain :
      drainB (x + 4) (tightB m) (2 * x + 5) =
        some (.D (x + m + 4) (3 * x + 3)) := by
    have h := (drainB_d3_exact_iff (x + 4) (tightB m) (2 * x + 5) m).2 rfl
    simpa [hthird, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  simp [highLevelNext, hxpos, hxeven, hxmod, hxdiv, heval, hdrain]

/-- The exact first step on the ratio-40 family. -/
theorem first_step (m : Nat) (hm : m % 2 = 0) :
    highLevelNext (.D (xFamily m) (40 * xFamily m)) =
      some (.D (39 * xFamily m + m + 2) (3 * xFamily m + 3)) := by
  let x := xFamily m
  have hxpos : 0 < x := by
    dsimp [x, xFamily]
    omega
  have hxeven : x % 2 = 0 := by
    simpa [x] using xFamily_even m hm
  have hbudget : x < ternaryOnes (x + 3) := by
    have h := ternaryOnes_ge (x + 3)
    omega
  have hbase := base_right_even m hm
  have hshift := highLevel_right_even_shift_ones x (2 * x + 2) (19 * x - 1)
    hxpos hxeven (by omega) (by omega) hbudget
  have hindex : 2 * x + 2 + 2 * (19 * x - 1) = 40 * x := by omega
  simpa [x, hindex, hbase, liftFirstState, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hshift

/-- A source-level exact far-left odd drain step when its block count is tight. -/
private theorem far_left_odd_tight (a d n : Nat)
    (hd : d % 2 = 1) (hfar : d + 5 ≤ a)
    (hblock : d + 3 = tightB n) :
    highLevelNext (.D a d) =
      some (.D (a - d - 5 + n) (5 + 3 * (d + 3))) := by
  have ha : a ≠ 0 := by omega
  have h := (drainB_d3_exact_iff (a - d - 5) (d + 3) 5 n).2 hblock
  simp [highLevelNext, ha, hd, hfar, h]

/-- Exact second step: the second block is tightB (m+2). -/
theorem second_step (m : Nat) (hm : m % 2 = 0) :
    highLevelNext (.D (39 * xFamily m + m + 2) (3 * xFamily m + 3)) =
      some (.D (36 * xFamily m + 2 * m - 4) (9 * xFamily m + 23)) := by
  let x := xFamily m
  have hxpos : 0 < x := by
    dsimp [x, xFamily]
    omega
  have hxeven : x % 2 = 0 := by
    simpa [x] using xFamily_even m hm
  have hdodd : (3 * x + 3) % 2 = 1 := by omega
  have hfar : 3 * x + 3 + 5 ≤ 39 * x + m + 2 := by omega
  have hblock : 3 * x + 6 = tightB (m + 2) := by
    dsimp [x, xFamily]
    simp [tightB]
    ring
  have hstep := far_left_odd_tight
    (39 * x + m + 2) (3 * x + 3) (m + 2) hdodd hfar hblock
  have hfirst : (39 * x + m + 2) - (3 * x + 3) - 5 + (m + 2) =
      36 * x + 2 * m - 4 := by omega
  have hthird : 5 + 3 * (3 * x + 6) = 9 * x + 23 := by omega
  simpa [x, hfirst, hthird] using hstep

/-- An exact zero-gap two-step source trajectory (take m = 48). -/
theorem two_step_zero_gap :
    ∃ x a d,
      highLevelNext (.D x (40 * x)) = some (.D a d) ∧
      highLevelNext (.D a d) = some (.D (4 * d) d) := by
  let m : Nat := 48
  let x := xFamily m
  let a := 39 * x + m + 2
  let d := 3 * x + 3
  have hm : m % 2 = 0 := by norm_num [m]
  refine ⟨x, a, d, ?_, ?_⟩
  · simpa [x, a, d, m] using first_step m hm
  · have h := second_step m hm
    have hgap : 36 * x + 2 * m - 4 = 4 * (9 * x + 23) := by
      norm_num [m]
    simpa [x, a, d, m, hgap] using h

end BB6.Agent49TwoStepPoleCancellation
