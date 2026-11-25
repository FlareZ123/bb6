import Agent49ParitySource
import BusyBeaver.BB6.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
import Lean.Elab.Tactic.Omega

namespace BB6.Agent48TerminalBudgetCounterexample

open BB6.Agent49ParitySource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Exact blank-root high-level orbit checkpoints around the synthetic
predecessor's mass. -/
theorem root_run_39 :
    run 39 = some (BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D 79788 133932) := by
  native_decide

theorem root_run_40 :
    run 40 = some (BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D 54138 239399) := by
  native_decide

/-- Mass is strictly increasing along any two surviving blank-root visits.
This iterates the source-level next_strict_mass inequality over the actual
run, not a simulator estimate. -/
theorem run_mass_mono (m : Nat) :
    ∀ n a d aa dd, m <= n →
      run m = some (BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D a d) →
      run n = some (BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D aa dd) →
      a + d <= aa + dd := by
  intro n
  induction n with
  | zero =>
    intro a d aa dd hmn hm hn
    have hm0 : m = 0 := by omega
    subst m
    have hEq : some (BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D a d) = some (BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D aa dd) := hm.symm.trans hn
    cases hEq
    omega
  | succ n ih =>
    intro a d aa dd hmn hm hn
    by_cases hmeq : m = n+1
    · subst m
      have hEq : some (BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D a d) = some (BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D aa dd) := hm.symm.trans hn
      cases hEq
      omega
    · have hmn' : m <= n := by omega
      cases hp : run n with
      | none => simp [run, hp] at hn
      | some s =>
        rcases s with ⟨b,c⟩
        have hstep : BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.highLevelNext (BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D b c) = some (BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D aa dd) := by
          simpa [run, hp] using hn
        have hprev := ih a d b c hmn' hm hp
        have hgain := next_strict_mass b c aa dd hstep
        omega

theorem root_run_41 :
    run 41 = some (BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D 185262 162438) := by
  native_decide

/-- Every surviving blank-root state is either before step 40, exactly the
step-40 state, or at/after step 41. The source mass jumps are large enough
that no other state can occupy the intervening mass interval. -/
theorem root_mass_gap_exclusion (n a d : Nat)
    (hseen : run n = some (BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D a d)) :
    a+d <= 213720 ∨
      (a = 54138 ∧ d = 239399) ∨
      347700 <= a+d := by
  by_cases hlt : n < 40
  · have hmono := run_mass_mono n 39 a d 79788 133932
      (by omega) hseen root_run_39
    exact Or.inl (by omega)
  · by_cases heq : n = 40
    · subst n
      have hEq : some (BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D 54138 239399) = some (BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D a d) :=
        root_run_40.symm.trans hseen
      cases hEq
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · have hge : 41 <= n := by omega
      have hmono := run_mass_mono 41 n 185262 162438 a d
        hge root_run_41 hseen
      exact Or.inr (Or.inr (by omega))

/-- Any candidate in the open step-39/step-41 mass corridor whose
second coordinate is below the step-40 second coordinate is not a root
state. This covers the full finite search domain in
scan_terminal_budget_family.js without enumerating its candidates. -/
theorem root_mass_corridor_excludes_small_d (n a d : Nat)
    (hseen : run n = some (BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D a d))
    (hlo : 213720 < a+d)
    (hhi : a+d < 347700)
    (hd : d < 239399) : False := by
  have hgap := root_mass_gap_exclusion n a d hseen
  rcases hgap with hsmall | hmid | hlarge
  · omega
  · rcases hmid with ⟨ha, hd'⟩
    omega
  · omega

/-- The exact synthetic budget witness is not on the genuine blank-root
orbit; it falls in the mass gap between the step-39 and step-41 checkpoints
and is not the unique step-40 state. -/
theorem synthetic_predecessor_not_blank_reachable (n : Nat) :
    run n ≠ some (BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D 260178 20001) := by
  intro hq
  have hgap := root_mass_gap_exclusion n 260178 20001 hq
  rcases hgap with hsmall | hmid | hlarge
  · omega
  · rcases hmid with ⟨ha, hd⟩
    omega
  · omega

/-- A second representative synthetic predecessor, closer to the n=10
band's lower edge, is likewise excluded by the blank-root mass gap. -/
theorem synthetic_predecessor2_not_blank_reachable (n : Nat) :
    run n ≠ some (BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D 256010 19681) := by
  intro hq
  have hgap := root_mass_gap_exclusion n 256010 19681 hq
  rcases hgap with hsmall | hmid | hlarge
  · omega
  · rcases hmid with ⟨ha, hd⟩
    omega
  · omega

/-- A third representative has the same total mass as the step-40 root
state but different coordinates, so the exact middle-state clause is
essential rather than a mass-only argument. -/
theorem synthetic_predecessor3_not_blank_reachable (n : Nat) :
    run n ≠ some (BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState.D 272586 20951) := by
  intro hq
  have hgap := root_mass_gap_exclusion n 272586 20951 hq
  rcases hgap with hsmall | hmid | hlarge
  · omega
  · rcases hmid with ⟨ha, hd⟩
    omega
  · omega

#print axioms root_run_39
#print axioms root_run_40
#print axioms root_run_41
#print axioms run_mass_mono
#print axioms root_mass_gap_exclusion
#print axioms root_mass_corridor_excludes_small_d
#print axioms synthetic_predecessor_not_blank_reachable

end BB6.Agent48TerminalBudgetCounterexample