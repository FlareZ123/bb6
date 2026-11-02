import Agent18BBridge
import BTraceReach
import BTraceRuntime
import Lean.Elab.Tactic.Omega

namespace BB6.BTrace
open BusyBeaver
open BB6.BReduction

/-- A local accelerated trace maps to a physical positive-step raw trace. -/
theorem accelerated_star_raw {s t : S} (h : Star s t) :
    ReachesStar BB6.Bridge.Source.target
      (BB6.Bridge.encodeB s) (BB6.Bridge.encodeB t) := by
  induction h with
  | refl => exact ReachesStar.refl _ _
  | step hs _ ih =>
      exact ((BB6.Bridge.is_valid_B.step_some _ _ hs).to_star).trans ih

/-- Each of the first n accelerated steps takes at least n raw TM steps. -/
theorem acceleration_lower_time (n : Nat) (s t : S)
    (h : runB n s = some t) :
    ∃ m : Nat, n ≤ m ∧
      ReachesIn BB6.Bridge.Source.target m (BB6.Bridge.encodeB s)
        (BB6.Bridge.encodeB t) := by
  induction n generalizing s with
  | zero =>
      have hst : s = t := Option.some.inj h
      subst t
      exact ⟨0, Nat.le_refl _, ReachesIn.zero _ _⟩
  | succ n ih =>
      have hh : (nextB s).bind (runB n) = some t := h
      cases hstep : nextB s with
      | none => simp [hstep] at hh
      | some u =>
          have hh' : runB n u = some t := by simpa only [hstep,Option.bind_some] using hh
          obtain ⟨m,hm,hr⟩ := ih u hh'
          obtain ⟨k,hk,hraw⟩ := BB6.Bridge.is_valid_B.step_some s u hstep
          exact ⟨k+m, by omega, ReachesIn.trans hraw hr⟩

/-- Original source: for every n below the exact fourth-reset index,
    the blank machine has a defined raw prefix of length at least n. -/
theorem raw_blank_below_fourth_reset (n : Nat)
    (hn : n < BB6.OneDim.scalarA 3) :
    ∃ m : Nat, n ≤ m ∧
      ∃ c, ReachesIn BB6.Bridge.Source.target m (init []) c := by
  obtain ⟨s,hs⟩ := runB_positive_fuel n (BB6.OneDim.scalarA 3,0,0) hn
  obtain ⟨k,hk,hraw⟩ := acceleration_lower_time n _ _ hs
  have hinit := BB6.Bridge.is_valid_B.init_reaches
  have hstarB : Star (3,0,0) (BB6.OneDim.scalarA 3,0,0) := by
    rw [BB6.OneDim.scalarA_eq_resetA 3]
    exact original_three_cycles_survive
  have hstar := accelerated_star_raw hstarB
  have hfrom := hinit.trans hstar
  obtain ⟨first,hfirst⟩ := hfrom
  refine ⟨first+k, by omega, BB6.Bridge.encodeB s, ?_⟩
  exact ReachesIn.trans hfirst hraw

#print axioms accelerated_star_raw
#print axioms acceleration_lower_time
#print axioms raw_blank_below_fourth_reset
end BB6.BTrace
