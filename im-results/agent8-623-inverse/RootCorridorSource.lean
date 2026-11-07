import Agent8ParentCorridorSource
import Agent8ZeroTailSource

/-!
Root-authenticated two-step terminal-parent restriction for genuine #623:
for every section index n from D(0,7), if the n-th state survives to a
daughter which halts immediately, the parent has positive even a, obeys
the source angular corridor, and fails every five-branch gate budget.
No assumption excluding future zero-a visits is required.

The proof uses exact source first four visits plus the certified universal
blank-root mass growth for all later visits. The theorem remains conditional
on a two-step terminal event and does not decide halting.
-/

namespace BB6.Agent8RootCorridorSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource

/-- At any genuine blank-root section visit, a zero-first-counter parent
cannot have a halting daughter. For n>=5 the strict mass bound makes d
large enough for the two-step source theorem; small indices are exact. -/
theorem blank_root_zero_a_no_immediate_daughter_halt (n d aa dd : Nat)
    (hseen : run n = some (.D 0 d))
    (hs : highLevelNext (.D 0 d) = some (.D aa dd)) :
    highLevelNext (.D aa dd) ≠ none := by
  by_cases hn : 5≤n
  · have hmass := run_grows_at_least_seven n 0 d hseen
    have hd : 40≤d := by omega
    obtain ⟨aa1,dd1,bb,ee,hfirst,hlast⟩ :=
      BB6.Agent8ZeroTailSource.zero_a_two_step d hd
    rw [hfirst] at hs
    cases hs
    simp [hlast]
  · have hcases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · subst n
      have hz : d=7 := by
        simp [run] at hseen
        cases hseen
        rfl
      subst d
      have hfirst := BB6.Agent8ZeroTailSource.zero_odd_source 7 (by decide)
      rw [hfirst] at hs
      have hnext : highLevelNext (.D 6 14) = some (.D 6 31) := by decide +kernel
      cases hs
      simp [hnext]
    · subst n
      have hv : run 1 = some (.D 6 14) := by decide +kernel
      rw [hv] at hseen
      cases hseen
    · subst n
      have hv : run 2 = some (.D 6 31) := by decide +kernel
      rw [hv] at hseen
      cases hseen
    · subst n
      have hv : run 3 = some (.D 26 26) := by decide +kernel
      rw [hv] at hseen
      cases hseen
    · subst n
      have hv : run 4 = some (.D 2 83) := by decide +kernel
      rw [hv] at hseen
      cases hseen

/-- Full rooted necessary corridor for any hypothetical two-step
terminal event. The positivity hypothesis is now proved, not assumed. -/
theorem blank_root_two_step_terminal_parent_corridor (n a d aa dd : Nat)
    (hseen : run n = some (.D a d))
    (hs : highLevelNext (.D a d) = some (.D aa dd))
    (hstop : highLevelNext (.D aa dd) = none) :
    0<a ∧
    (d%2=1 → d<16*a ∧ a<16*d+68) ∧
    (d%2=0 → d<14*a+24 ∧ a<16*d+44) ∧
    (∀k, ¬ BB6.Agent8GateCompleteSource.gateBudget a d k) := by
  have ha : 0<a := by
    by_cases hz : a=0
    · subst a
      have hf := blank_root_zero_a_no_immediate_daughter_halt n d aa dd hseen hs
      exact False.elim (hf hstop)
    · omega
  exact ⟨ha,BB6.Agent8ParentCorridorSource.blank_two_step_terminal_parent_corridor
    n a d aa dd hseen ha hs hstop⟩

#print axioms blank_root_zero_a_no_immediate_daughter_halt
#print axioms blank_root_two_step_terminal_parent_corridor
end BB6.Agent8RootCorridorSource
