import RootMassGapAllN10
import Lean.Elab.Tactic.Omega

/-!
# n=10 exclusion of the exceptional even gap-two root branch

This is a root-specific mass-gap argument. It excludes the branch
D(d+2,d), 19680 <= d <= 59045, from the genuine blank-root orbit.
The only new source checkpoint is run 32; all later checkpoints are
imported from RootMassGapAllN10.
-/

namespace BB6.Agent48N10GapTwoExclusion

open BB6.Agent49ParitySource
open BB6.Agent48TerminalBudgetCounterexample
open BB6.Agent8RootMassGapAllN10

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Exact blank-root checkpoint immediately before the n=10 near corridor. -/
theorem root_run_32 :
    run 32 = some (.D 29194 9235) := by
  decide

/-- No genuine blank-root visit in the n=10 scale band is in the
exceptional even branch a=d+2. Its mass would lie strictly between
the exact masses at steps 32 and 37, leaving only steps 33--36. -/
theorem n10_even_gap_two_root_excluded (n a d : Nat)
    (hseen : run n = some (.D a d))
    (hmLo : 19680 <= d) (hmHi : d <= 59045)
    (hgap : a = d+2) : False := by
  have hmassLo : 39362 <= a+d := by omega
  have hmassHi : a+d <= 118092 := by omega
  have hnotLo : ¬ n <= 32 := by
    intro hn
    have hm := run_mass_mono n 32 a d 29194 9235 hn hseen root_run_32
    omega
  have hnotHi : ¬ 37 <= n := by
    intro hn
    have hm := run_mass_mono 37 n 41468 86104 hn root_run_37 hseen
    omega
  have hcases : n = 33 ∨ n = 34 ∨ n = 35 ∨ n = 36 := by omega
  rcases hcases with h33 | h34 | h35 | h36
  · subst n
    have hEq : some (.D 19954 27733) = some (.D a d) :=
      root_run_33.symm.trans hseen
    cases hEq
    omega
  · subst n
    have hEq : some (.D 7784 59872) = some (.D a d) :=
      root_run_34.symm.trans hseen
    cases hEq
    omega
  · subst n
    have hEq : some (.D 52084 23375) = some (.D a d) :=
      root_run_35.symm.trans hseen
    cases hEq
    omega
  · subst n
    have hEq : some (.D 28698 70161) = some (.D a d) :=
      root_run_36.symm.trans hseen
    cases hEq
    omega

#print axioms root_run_32
#print axioms n10_even_gap_two_root_excluded

end BB6.Agent48N10GapTwoExclusion
