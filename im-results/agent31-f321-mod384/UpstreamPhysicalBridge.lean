import BusyBeaver.BB6.M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD
import Mod384Source
import HaltingBridgeCore
import Lean.Elab.Tactic.Omega

/-!
The fully source-authentic physical-machine bridge for the F321
parity-aware 384 quotient. The imported upstream proof constructs a
halting-equivalent high-level acceleration of the original six-state
machine. We connect the *unchanged* highLevelNext to our independently
source-kernel checked CounterMove and restrict the terminal parameter.

This does not assert nonhalting of the original machine!
-/
namespace BB6.Agent31F321Physical
open BB6.Agent31F321Density
open BB6.Agent31F321Mod384
open BusyBeaver
open BusyBeaver.M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD

/-- An option-valued map can first become `none` only immediately after
    some finite genuine trace ending at a state with `next = none`. -/
theorem eventually_none_has_terminal {S : Type} (f : S → Option S)
    (s : S) (h : ∃ n : Nat,
    ((Option.bind · f)^[n] (some s)).isNone) :
    ∃ (m : Nat) (t : S), OptTrace f s m t ∧ f t = none := by
  rcases h with ⟨n,hn⟩
  induction n generalizing s with
  | zero => simp at hn
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hn
      cases hs : f s with
      | none => exact ⟨0,s,OptTrace.nil,hs⟩
      | some s' =>
          have hn' : ((Option.bind · f)^[n] (some s')).isNone := by
            simpa [hs] using hn
          obtain ⟨m,t,hr,ht⟩ := ih s' hn'
          exact ⟨m+1,t,OptTrace.prepend hs hr,ht⟩


/-- Erase the upstream single-constructor high-level state wrapper. -/
def decodeUpstream : HighLevelState → Nat × Nat
 | .P a d => (a,d)

/-- Exact, *unmodified* pinned upstream high-level transition agrees
    branch-for-branch with our source-counter transition. -/
theorem source_next_upstream (s : HighLevelState) :
  pairSourceNext (decodeUpstream s) =
    (highLevelNext s).map decodeUpstream := by
  cases s with
  | P a d =>
      have hHigh : (d+1<a) = (a≥d+2) := propext (by omega)
      have hFar : (3*a<d) = (3*a+1≤d) := propext (by omega)
      simp [sourceNext, highLevelNext, pairSourceNext, decodeUpstream,
        hHigh, hFar]

/-- Every genuine upstream high-level trace decodes to a source-counter
    trace, and hence is covered by the exact parity-residue certificate. -/
theorem upstream_trace_to_source {n : Nat} {s : HighLevelState}
   (hr : OptTrace highLevelNext highLevelStart n s) :
   OptTrace pairSourceNext (1,1) n (decodeUpstream s) := by
  induction hr with
  | nil => exact OptTrace.nil
  | @step m a b hr hs ih =>
      apply OptTrace.step ih
      rw [source_next_upstream]
      simp [hs]

/-- A *real, originally encoded six-state F321 halt from blank tape*
    forces the actual counter halting parameter into the fifteen classes.
    This statement makes the original-machine bridge explicit and stops
    short of deciding the remaining gate classes or global BB(6). -/
theorem original_blank_halt_implies_mod384_terminal
  (hh : BusyBeaver.IsHalt target) :
    ∃ (d n : Nat), CounterReach 1 1 n (d+1) d ∧ d % 384 ∈ possibleGates := by
  have hc : BusyBeaver.CollatzHalts highLevelNext highLevelStart :=
    isHalt_iff_highLevel_acceleration.mp hh
  obtain ⟨n,s,hr,hs⟩ :=
    eventually_none_has_terminal highLevelNext highLevelStart hc
  have htrace := upstream_trace_to_source hr
  have hstop : pairSourceNext (decodeUpstream s) = none := by
    rw [source_next_upstream]
    simp [hs]
  cases s with
  | P a d =>
      have hreach : CounterReach 1 1 n a d := by
        simpa [decodeUpstream] using source_trace_counter htrace
      have hnone : sourceNext a d = none := by
        simpa [decodeUpstream,pairSourceNext] using hstop
      have hterminal : a=d+1 := (sourceNext_none_iff a d).mp hnone
      subst a
      exact ⟨d,n,hreach,terminal_mod384_candidates d n hreach⟩

#print axioms eventually_none_has_terminal
#print axioms source_next_upstream
#print axioms upstream_trace_to_source
#print axioms original_blank_halt_implies_mod384_terminal
end BB6.Agent31F321Physical
