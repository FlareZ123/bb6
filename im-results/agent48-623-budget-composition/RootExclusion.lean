import Agent49ParitySource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent48TerminalBudgetCounterexample

open BB6.Agent49ParitySource

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Exact blank-root high-level orbit checkpoints around the synthetic
predecessor's mass. -/
theorem root_run_39 :
    run 39 = some (.D 79788 133932) := by
  decide

theorem root_run_40 :
    run 40 = some (.D 54138 239399) := by
  decide

/-- Mass is strictly increasing along any two surviving blank-root visits.
This iterates the source-level next_strict_mass inequality over the actual
run, not a simulator estimate. -/
theorem run_mass_mono (m : Nat) :
    ∀ n a d aa dd, m <= n →
      run m = some (.D a d) →
      run n = some (.D aa dd) →
      a + d <= aa + dd := by
  intro n
  induction n with
  | zero =>
    intro a d aa dd hmn hm hn
    have hm0 : m = 0 := by omega
    subst m
    have hEq : some (.D a d) = some (.D aa dd) := hm.symm.trans hn
    cases hEq
    omega
  | succ n ih =>
    intro a d aa dd hmn hm hn
    by_cases hmeq : m = n+1
    · subst m
      have hEq : some (.D a d) = some (.D aa dd) := hm.symm.trans hn
      cases hEq
      omega
    · have hmn' : m <= n := by omega
      cases hp : run n with
      | none => simp [run, hp] at hn
      | some s =>
        rcases s with ⟨b,c⟩
        have hstep : next (.D b c) = some (.D aa dd) := by
          simpa [run, hp] using hn
        have hprev := ih a d b c hmn' hm hp
        have hgain := next_strict_mass b c aa dd hstep
        omega

/-- The exact synthetic budget witness is not on the genuine blank-root
orbit: before step 40 the root mass is at most 213720; from step 40 onward
it is at least 293537, whereas the witness has mass 280179. -/
theorem synthetic_predecessor_not_blank_reachable (n : Nat) :
    run n ≠ some (.D 260178 20001) := by
  intro hq
  by_cases hlt : n < 40
  · have hmono := run_mass_mono n 39 260178 20001 79788 133932
      (by omega) hq root_run_39
    norm_num at hmono
  · have hmono := run_mass_mono 40 n 54138 239399 260178 20001
      (by omega) root_run_40 hq
    norm_num at hmono

#print axioms root_run_39
#print axioms root_run_40
#print axioms run_mass_mono
#print axioms synthetic_predecessor_not_blank_reachable

end BB6.Agent48TerminalBudgetCounterexample