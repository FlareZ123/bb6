import Agent8RootCorridorSource

/-!
Genuine blank-origin terminal witness reduction for Cryptids #623.
If a section state on the authentic orbit ever halts, then it has
an actual preceding successful source section whose positive first
counter, angular coordinates, and five disjoint branch budgets obey
the root-proved two-step terminal-parent restrictions. The terminal
state independently satisfies the source power-of-three gap.

This is a universal conditional theorem over all section indices.
It leaves existence of such a state open.
-/

namespace BB6.Agent8HaltParentSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource

/-- Source blank section zero survives and reaches the first exact visit. -/
theorem root_zero_section_safe :
    highLevelNext (.D 0 7) = some (.D 6 14) := by
  decide +kernel

/-- Any hypothetical terminal source section on the genuine blank orbit
has a real predecessor outside every five-branch gate budget and inside
the explicit parity-dependent angular corridor; its terminal daughter
obeys the independently proved power-of-three halting gap. -/
theorem blank_terminal_halt_with_parent (n a d : Nat)
    (hseen : run n=some (.D a d))
    (hhalt : highLevelNext (.D a d)=none) :
    ∃ m p q, run m=some (.D p q) ∧
      highLevelNext (.D p q)=some (.D a d) ∧
      0<p ∧
      (q%2=1 → q<16*p ∧ p<16*q+68) ∧
      (q%2=0 → q<14*p+24 ∧ p<16*q+44) ∧
      (∀k, ¬ BB6.Agent8GateCompleteSource.gateBudget p q k) ∧
      (3^(d-a-5) ≤ 2*(a+d)+5 ∧ 3^(a-d-5) ≤ 2*(a+d)+5) := by
  have hgate := blank_run_requires_pow_gap n a d hseen hhalt
  cases n with
  | zero =>
    have ha0 : a=0 ∧ d=7 := by
      simp [run] at hseen
      omega
    rcases ha0 with ⟨ha,hd⟩
    subst a
    subst d
    simp [root_zero_section_safe] at hhalt
  | succ m =>
    cases hp : run m with
    | none => simp [run,hp] at hseen
    | some s =>
      rcases s with ⟨p,q⟩
      have hstep : highLevelNext (.D p q)=some (.D a d) := by
        simpa only [run,hp,Option.bind_some] using hseen
      have hcorr :=
        BB6.Agent8RootCorridorSource.blank_root_two_step_terminal_parent_corridor
          m p q a d hp hstep hhalt
      exact ⟨m,p,q,hp,hstep,hcorr.1,hcorr.2.1,
        hcorr.2.2.1,hcorr.2.2.2,hgate⟩

#print axioms root_zero_section_safe
#print axioms blank_terminal_halt_with_parent
end BB6.Agent8HaltParentSource
