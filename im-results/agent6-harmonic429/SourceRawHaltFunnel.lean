import SourceMod32Six
import Lean.Elab.Tactic.Omega

namespace BB429ActualHaltFunnel
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

/-- Our primitive recursive accelerated sourceRun coincides with the
    iterate semantics in the original Cryptids CollatzHalts definition. -/
theorem source_run_eq_iterate (n : Nat) (s : HighLevelState) :
    BB429SourceLadder.sourceRun n s =
      ((Option.bind · highLevelNext)^[n]) (some s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simp only [BB429SourceLadder.sourceRun, ih]

/-- Any finite transition chain ending in none has a last successful state. -/
theorem source_none_has_last (n : Nat) (s : HighLevelState)
    (h : BB429SourceLadder.sourceRun n s = none) :
    ∃ k t, BB429SourceLadder.sourceRun k s = some t ∧
      highLevelNext t = none := by
  induction n with
  | zero =>
    simp [BB429SourceLadder.sourceRun] at h
  | succ n ih =>
    simp only [BB429SourceLadder.sourceRun] at h
    cases hp : BB429SourceLadder.sourceRun n s with
    | none => exact ih hp
    | some t =>
      refine ⟨n,t,hp,?_⟩
      simpa only [hp,Option.bind_some] using h

/-- This is about the true six-state raw Turing machine, not an arbitrary
    synthetic accelerated seed. Every hypothetical blank-tape halt must pass
    through one of the six globally necessary modulo-32 high-level gates. -/
theorem actual_machine_halt_requires_six_gate (h : IsHalt target) :
    ∃ n u w,
      BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
      highLevelNext (.J u w) = none ∧
      (u%32=3 ∨ u%32=9 ∨ u%32=17 ∨ u%32=21 ∨
       u%32=25 ∨ u%32=29) := by
  obtain ⟨n, hn⟩ := isHalt_iff_highLevel_acceleration.mp h
  have hiter : ((Option.bind · highLevelNext)^[n] (some highLevelStart)) = none := by
    cases hi : ((Option.bind · highLevelNext)^[n] (some highLevelStart)) with
    | none => exact hi
    | some t => simp [hi] at hn
  have hrun : BB429SourceLadder.sourceRun n highLevelStart = none := by
    rw [source_run_eq_iterate]
    exact hiter
  obtain ⟨k,t,hk,ht⟩ := source_none_has_last n highLevelStart hrun
  cases t with
  | J u w =>
    exact ⟨k,u,w,hk,ht,
      BB429SourceMod32Six.source_halting_mod32_six k u w hk ht⟩

#print axioms source_run_eq_iterate
#print axioms source_none_has_last
#print axioms actual_machine_halt_requires_six_gate
end BB429ActualHaltFunnel
