import Agent8RootSpectrumSource

/-!
The genuine blank-start #623 return can only halt from a state with
third counter at least 23. This uses the all-time source-root spectrum,
the existing mass growth and far-left safe corridor, and seven exact
initial return computations. It does not decide halting.
-/
namespace BB6.Agent8TerminalSpectrumSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent8RootSpectrumSource

theorem run_none_stays (n k : Nat) (h : run n = none) : run (n+k)=none := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have hstep : run (n+(k+1)) = (run (n+k)).bind highLevelNext := by
      rw [show n+(k+1)=(n+k)+1 by omega,run]
    rw [hstep, ih]
    rfl

/-- The first seven actual accelerated returns are successful. -/
theorem run_seven_survives : (run 7).isSome := by decide +kernel

/-- All possible genuine blank-origin halting sections have d >= 23. -/
theorem terminal_d_ge_23 (n a d : Nat)
  (hs : run n = some (.D a d))
  (hh : highLevelNext (.D a d)=none) : 23≤d := by
  by_cases h23 : 23 ≤ d
  · exact h23
  · have spec := run_low_third_spectrum n a d hs
    have hd : d≤14 := by omega
    have hnear := next_none_requires_corridor a d (run_preserves_even n a d hs) hh
    have hm := run_grows_at_least_seven n a d hs
    have hn6 : n≤6 := by omega
    have hnext : run (n+1)=none := by simp [run,hs,hh]
    have hshift : n+1+(6-n)=7 := by omega
    have hseven : run 7 = none := by
      rw [←hshift]
      exact run_none_stays (n+1) (6-n) hnext
    have hsurvive := run_seven_survives
    rw [hseven] at hsurvive
    contradiction

#print axioms run_seven_survives
#print axioms terminal_d_ge_23
end BB6.Agent8TerminalSpectrumSource
