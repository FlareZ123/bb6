import Agent27GapTwoArithmetic
import Agent8RootCorridorSource
import Lean.Elab.Tactic.Omega
namespace BB6.Agent27GapTwoThreeStepSource
open BusyBeaver.BB6.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent27GapTwoArithmetic
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def gapTwoVisit : Option HighLevelState → Bool
  | none => false
  | some (.D a d) => decide (a = d+2)
theorem no_small_root_gap_two (t a d : Nat)
    (hseen : run t = some (.D a d)) (hgap : a = d+2)
    (ha : a < 32) : False := by
  have hm := run_grows_at_least_seven t a d hseen
  have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by omega
  have hz : gapTwoVisit (run t) = false := by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  simp [hseen, gapTwoVisit, hgap] at hz
theorem large_even_gap_two_exit (a d x y : Nat)
    (ha : 32 ≤ a) (he : a%2 = 0) (hgap : a = d+2)
    (hstep : highLevelNext (.D a d) = some (.D x y)) : 16*x+24 ≤ y := by
  have h0 : a ≠ 0 := by omega
  have h1 : ¬(d%2 = 1 ∧ a ≥ d+5) := by omega
  have h2 : ¬(d%2 = 0 ∧ a ≥ d+3) := by omega
  have h3 : a%2 ≠ 1 := by omega
  simp only [highLevelNext, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos hgap] at hstep
  have hf := BB6.Agent8GateRepulsionSource.drainB_first_le_pow
    (a/8) 0 a 2 x y (gap_two_depth a ha) hstep
  have hd := BB6.Agent8BudgetSource.drainB_d3 a 0 2 x y hstep
  exact gap_two_output_outside_corridor a x y ha (by omega) (by omega)
theorem blank_root_gap_two_no_three_step_terminal
    (t a d x y aa dd : Nat)
    (hseen : run t = some (.D a d)) (hgap : a = d+2)
    (hstep : highLevelNext (.D a d) = some (.D x y))
    (hnext : highLevelNext (.D x y) = some (.D aa dd))
    (hhalt : highLevelNext (.D aa dd) = none) : False := by
  have ha : 32 ≤ a := by
    by_cases h : 32 ≤ a
    · exact h
    · exact (no_small_root_gap_two t a d hseen hgap (by omega)).elim
  have he := run_preserves_even t a d hseen
  have hbound := large_even_gap_two_exit a d x y ha he hgap hstep
  have hpseen : run (t+1) = some (.D x y) := by
    simp only [run, hseen, Option.bind_some]
    exact hstep
  obtain ⟨hpos,hodd,heven,hgate⟩ :=
    BB6.Agent8RootCorridorSource.blank_root_two_step_terminal_parent_corridor
      (t+1) x y aa dd hpseen hnext hhalt
  by_cases hy : y%2 = 1
  · have hc := (hodd hy).1
    omega
  · have hy0 : y%2 = 0 := by omega
    have hc := (heven hy0).1
    omega
#print axioms no_small_root_gap_two
#print axioms large_even_gap_two_exit
#print axioms blank_root_gap_two_no_three_step_terminal
end BB6.Agent27GapTwoThreeStepSource
