import Agent8LogConeSource
import Agent8RootCorridorSource

/-!
All-time source #623 logarithmic outer-sector exclusions for genuine
blank-root terminal parents. Conditions are necessary for hypothetical
two-step terminal events and do not establish the machine's outcome.
-/

namespace BB6.Agent8LogParentSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

def logOuterBudget (a d k : Nat) : Prop :=
  (d%2=1 ∧ 9*d+39+k≤a ∧ 14*d+59≤3^k) ∨
  (d%2=0 ∧ 9*d+25+k≤a ∧ 14*d+39≤3^k) ∨
  (d%2=1 ∧ 9*a+k≤d+4 ∧ 14*a≤3^k) ∨
  (d%2=0 ∧ 8*a+13+k≤d ∧ 12*a+23≤3^k)

theorem two_step_terminal_excludes_log (a d aa dd : Nat)
    (ha : 0<a) (he : a%2=0)
    (hs : highLevelNext (.D a d)=some (.D aa dd))
    (hstop : highLevelNext (.D aa dd)=none) :
    ∀ k, ¬ logOuterBudget a d k := by
  intro k hlog
  unfold logOuterBudget at hlog
  rcases hlog with h1|h2|h3|h4
  · rcases h1 with ⟨hd,hr,hp⟩
    obtain ⟨b,e,hb⟩ := BB6.Agent8LogOuterSource.odd_far_left_log_two_step
      a d k aa dd ha hd hr hp hs
    simp [hb] at hstop
  · rcases h2 with ⟨hd,hr,hp⟩
    obtain ⟨b,e,hb⟩ := BB6.Agent8LogOuterSource.even_far_left_log_two_step
      a d k aa dd ha hd hr hp hs
    simp [hb] at hstop
  · rcases h3 with ⟨hd,hr,hp⟩
    obtain ⟨b,e,hb⟩ := BB6.Agent8LogOuterSource.odd_far_right_log_two_step
      a d k aa dd ha he hd hr hp hs
    simp [hb] at hstop
  · rcases h4 with ⟨hd,hr,hp⟩
    obtain ⟨b,e,hb⟩ := BB6.Agent8LogOuterSource.even_far_right_log_two_step
      a d k aa dd ha he hd hr hp hs
    simp [hb] at hstop

theorem blank_terminal_excludes_log (n a d aa dd : Nat)
    (hseen : BB6.Agent49ParitySource.run n=some (.D a d))
    (hs : highLevelNext (.D a d)=some (.D aa dd))
    (hstop : highLevelNext (.D aa dd)=none) :
    0<a ∧ ∀ k, ¬ logOuterBudget a d k := by
  have hc := BB6.Agent8RootCorridorSource.blank_root_two_step_terminal_parent_corridor
    n a d aa dd hseen hs hstop
  have he := BB6.Agent49ParitySource.run_preserves_even n a d hseen
  exact ⟨hc.1, two_step_terminal_excludes_log a d aa dd hc.1 he hs hstop⟩

#print axioms two_step_terminal_excludes_log
#print axioms blank_terminal_excludes_log
end BB6.Agent8LogParentSource
