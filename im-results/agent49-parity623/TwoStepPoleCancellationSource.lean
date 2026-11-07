import Agent8BudgetSource

/-!
A synthetic two-step cancellation family for Cryptids #623.

This is an exact trajectory of the original high-level source map, but it is
not claimed to be reachable from the blank root. It demonstrates that the
projective two-step pole can be attained after the exact ternary-drain
corrections on states elsewhere in the admissible cone.
-/

namespace BB6.Agent49TwoStepPoleCancellation

open BB6.Agent49ParitySource
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
  simp [xFamily, tightB_mod_two]

/-- Exact first step on the synthetic ratio-40 family. -/
theorem first_step (m : Nat) (hm : m % 2 = 0) :
    highLevelNext (.D (xFamily m) (40 * xFamily m)) =
      some (.D (39 * xFamily m + m + 2) (3 * xFamily m + 3)) := by
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
  have harg : 40 * x + 1 - x = 39 * x + 1 := by omega
  have heval :
      evalA (39 * x + 1) x (2 * x + 5) =
        some (39 * x + 2, tightB m, 2 * x + 5) := by
    rw [evalA]
    simp [hxmod, hxdiv]
  have hthird : 2 * x + 5 + 3 * tightB m = 3 * x + 3 := by
    dsimp [x, xFamily]
    omega
  have hdrain :
      drainB (39 * x + 2) (tightB m) (2 * x + 5) =
        some (.D (39 * x + m + 2) (3 * x + 3)) := by
    simpa [hthird, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      drainB_tight m (39 * x + 2) (2 * x + 5)
  change highLevelNext (.D x (40 * x)) =
    some (.D (39 * x + m + 2) (3 * x + 3))
  simp [highLevelNext, hxpos, hxeven, harg, heval, hdrain]

/-- A source-level exact far-left odd step when its drain block is tight. -/
private theorem far_left_odd_tight (a d n : Nat)
    (hd : d % 2 = 1) (hfar : d + 5 ≤ a)
    (hblock : d + 3 = tightB n) :
    highLevelNext (.D a d) =
      some (.D (a - d - 5 + n) (5 + 3 * (d + 3))) := by
  have ha : a ≠ 0 := by omega
  have hdrain :
      drainB (a - d - 5) (d + 3) 5 =
        some (.D (a - d - 5 + n) (5 + 3 * (d + 3))) := by
    rw [hblock]
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      drainB_tight n (a - d - 5) 5
  simp [highLevelNext, ha, hd, hfar, hdrain]

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
  have hfirst :
      39 * x + m - (3 * x + 1) - 5 + (m + 2) =
        36 * x + 2 * m - 4 := by omega
  have hthird : 5 + 3 * (3 * x + 6) = 9 * x + 23 := by omega
  simpa [hfirst, hthird] using hstep

/-- An exact zero-gap two-step source trajectory (take m = 48). -/
theorem two_step_zero_gap :
    ∃ x a b d,
      highLevelNext (.D x (40 * x)) = some (.D a b) ∧
      highLevelNext (.D a b) = some (.D (4 * d) d) := by
  let m : Nat := 48
  let x := xFamily m
  let a := 39 * x + m + 2
  let b := 3 * x + 3
  let d := 9 * x + 23
  have hm : m % 2 = 0 := by norm_num [m]
  refine ⟨x, a, b, d, ?_, ?_⟩
  · simpa [x, a, b, m] using first_step m hm
  · have h := second_step m hm
    have hgap : 36 * x + 2 * m - 4 = 4 * (9 * x + 23) := by
      dsimp [m]
      ring
    simpa [x, a, b, d, m, hgap] using h

end BB6.Agent49TwoStepPoleCancellation
