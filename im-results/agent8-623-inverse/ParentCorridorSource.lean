import Agent8FarSectorSource
import Agent8GateCompleteSource

/-!
Original-source necessary corridor for a two-step terminal event in #623.
The last successful parent may belong only to the angular bounds below
and must fail all five explicit gate budgets. This theorem also specializes
to authentic blank-start section orbits at every n using the source parity
invariant. It does not establish that a terminal event ever occurs.
-/

namespace BB6.Agent8ParentCorridorSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- Universal necessary source corridor for a successful parent whose
immediate successor fails its next accelerated transition. -/
theorem two_step_terminal_parent_corridor (a d aa dd : Nat)
    (ha : 0<a) (he : a%2=0)
    (hs : highLevelNext (.D a d) = some (.D aa dd))
    (hstop : highLevelNext (.D aa dd) = none) :
    (d%2=1 → d < 16*a ∧ a < 16*d+68) ∧
    (d%2=0 → d < 14*a+24 ∧ a < 16*d+44) ∧
    (∀ k, ¬ BB6.Agent8GateCompleteSource.gateBudget a d k) := by
  constructor
  · intro hodd
    constructor
    · by_cases hc : d < 16*a
      · exact hc
      · have hfar : 16*a ≤ d := by omega
        obtain ⟨bb,ee,hn⟩ := BB6.Agent8FarSectorSource.odd_far_right_two_step
          a d aa dd ha he hodd hfar hs
        simp [hn] at hstop
    · by_cases hc : a < 16*d+68
      · exact hc
      · have hfar : 16*d+68 ≤ a := by omega
        obtain ⟨bb,ee,hn⟩ := BB6.Agent8FarSectorSource.odd_far_left_two_step
          a d aa dd ha hodd hfar hs
        simp [hn] at hstop
  constructor
  · intro heven
    constructor
    · by_cases hc : d < 14*a+24
      · exact hc
      · have hfar : 14*a+24 ≤ d := by omega
        obtain ⟨bb,ee,hn⟩ := BB6.Agent8FarSectorSource.even_far_right_two_step
          a d aa dd ha he heven hfar hs
        simp [hn] at hstop
    · by_cases hc : a < 16*d+44
      · exact hc
      · have hfar : 16*d+44 ≤ a := by omega
        obtain ⟨bb,ee,hn⟩ := BB6.Agent8FarSectorSource.even_far_left_two_step
          a d aa dd ha heven hfar hs
        simp [hn] at hstop
  · intro k hb
    obtain ⟨bb,ee,hn⟩ := BB6.Agent8GateCompleteSource.gate_budget_two_step
      a d k aa dd ha he hb hs
    simp [hn] at hstop

/-- The same condition for any actual rooted section visit from D(0,7). -/
theorem blank_two_step_terminal_parent_corridor (n a d aa dd : Nat)
    (hseen : BB6.Agent49ParitySource.run n = some (.D a d))
    (ha : 0<a)
    (hs : highLevelNext (.D a d) = some (.D aa dd))
    (hstop : highLevelNext (.D aa dd) = none) :
    (d%2=1 → d < 16*a ∧ a < 16*d+68) ∧
    (d%2=0 → d < 14*a+24 ∧ a < 16*d+44) ∧
    (∀ k, ¬ BB6.Agent8GateCompleteSource.gateBudget a d k) := by
  have he := BB6.Agent49ParitySource.run_preserves_even n a d hseen
  exact two_step_terminal_parent_corridor a d aa dd ha he hs hstop

#print axioms two_step_terminal_parent_corridor
#print axioms blank_two_step_terminal_parent_corridor
end BB6.Agent8ParentCorridorSource
