import NeedleGrowthFinite
import NeedleGrowthSource
import SpaceNeedleRawBridge
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20.SpaceNeedleGrowth
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- The original source high-level transition, iterated on the genuine
    blank-start value. -/
private noncomputable def sourceRun : Nat → Option HighLevelState
  | 0 => some highLevelStart
  | n+1 => (sourceRun n).bind highLevelNext

private theorem sourceRun_eq_iter (n : Nat) :
    sourceRun n = Nat.iterate
      (fun z : Option HighLevelState => z.bind highLevelNext)
      n (some highLevelStart) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (sourceRun n).bind highLevelNext = _
      rw [ih]
      rw [Nat.add_comm n 1, Function.iterate_add_apply]
      rfl

/-- Every earlier state on a successfully completed finite high-level
    source trace is also defined. -/
private theorem sourceRun_prefix (n : Nat) :
    ∀ i, i ≤ n → (∃ d, sourceRun n = some (.N d)) →
      ∃ d, sourceRun i = some (.N d) := by
  induction n with
  | zero =>
      intro i hi hd
      have heq : i = 0 := by omega
      subst i
      exact hd
  | succ n ih =>
      intro i hi hd
      by_cases heq : i=n+1
      · simpa [heq] using hd
      · have hi' : i ≤ n := by omega
        obtain ⟨d,hdn⟩ := hd
        have hprev : ∃ p, sourceRun n=some (.N p) := by
          change (sourceRun n).bind highLevelNext = some (.N d) at hdn
          cases hr : sourceRun n with
          | none => simp [hr] at hdn
          | some state =>
              cases state with
              | N p => exact ⟨p,rfl⟩
        exact ih i hi' hprev

private noncomputable def sourceCounter (i : Nat) : Nat :=
  match sourceRun i with
  | some (.N d) => d
  | none => 0

private theorem sourceCounter_spec (i d : Nat)
    (h : sourceRun i = some (.N d)) : sourceCounter i=d := by
  simp [sourceCounter,h]

/-- Every source-defined finite return prefix obeys a superlinear
    lower bound, irrespective of the future halting question. -/
theorem original_finite_run_superlinear (d n M : Nat)
    (hr : sourceRun n = some (.N d)) (hn : 2^(M+1) ≤ n) :
    (n/2)*(M+2) ≤ d+2 := by
  have hprefix : NeedleGrowth.Prefix (fun i => sourceCounter i+2) n := by
    intro i hi
    obtain ⟨p,hp⟩ := sourceRun_prefix n i (by omega) ⟨d,hr⟩
    obtain ⟨e,he⟩ := sourceRun_prefix n (i+1) (by omega) ⟨d,hr⟩
    have hstep : highLevelNext (.N p) = some (.N e) := by
      have hh := he
      change (sourceRun i).bind highLevelNext = some (.N e) at hh
      rw [hp] at hh
      simpa using hh
    have hh := original_edge p e hstep
    simpa [sourceCounter_spec i p hp, sourceCounter_spec (i+1) e he] using hh
  have hh := NeedleGrowth.prefix_superlinear (fun i => sourceCounter i+2) n M n hprefix (by omega) hn
  rw [sourceCounter_spec n d hr] at hh
  exact hh

/-- Authenticate the finite-prefix theorem for the original high-level
    iterate from the original blank start. -/
theorem original_iterate_superlinear (d n M : Nat)
    (hr : Nat.iterate (fun z : Option HighLevelState => z.bind highLevelNext)
        n (some highLevelStart) = some (.N d))
    (hn : 2^(M+1) ≤ n) :
    (n/2)*(M+2) ≤ d+2 := by
  apply original_finite_run_superlinear d n M
  · rw [sourceRun_eq_iter]
    exact hr
  · exact hn

/-- Every genuine blank-reachable source counter has an arrival time
    obeying a precise dyadic logarithmic restriction. -/
theorem genuine_root_time_bound (d M : Nat) (h : ReachN d) :
    ∃ n, (n < 2^(M+1) ∨ (n/2)*(M+2) ≤ d+2) := by
  rcases h with ⟨n,hn⟩
  refine ⟨n,?_⟩
  by_cases hbig : 2^(M+1) ≤ n
  · exact Or.inr (original_iterate_superlinear d n M hn hbig)
  · exact Or.inl (by omega)

#print axioms BB6.Agent20.SpaceNeedleGrowth.original_finite_run_superlinear
#print axioms BB6.Agent20.SpaceNeedleGrowth.original_iterate_superlinear
#print axioms BB6.Agent20.SpaceNeedleGrowth.genuine_root_time_bound
end BB6.Agent20.SpaceNeedleGrowth
