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

namespace BB6.Agent20.SpaceNeedleGrowth
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- An explicit, algorithmically useful bound on the number of
    high-level steps required to reach a prescribed genuine target. -/
theorem original_iterate_time_upper (d n M : Nat)
    (hr : Nat.iterate (fun z : Option HighLevelState => z.bind highLevelNext)
        n (some highLevelStart) = some (.N d)) :
    n < 2^(M+1) ∨ n ≤ 2*((d+2)/(M+2))+1 := by
  by_cases hn : 2^(M+1) ≤ n
  · right
    have hh := original_iterate_superlinear d n M hr hn
    have hdiv : n/2 ≤ (d+2)/(M+2) :=
      (Nat.le_div_iff_mul_le (by omega)).mpr hh
    have hmul := Nat.mul_le_mul_left 2 hdiv
    omega
  · left
    omega

/-- A closed-form logarithmic-in-step-index lower bound, unconditional
    for any authentic finite successful blank-root trace. -/
theorem original_iterate_log_growth (d n : Nat)
    (hr : Nat.iterate (fun z : Option HighLevelState => z.bind highLevelNext)
        n (some highLevelStart) = some (.N d)) (h2 : 2 ≤ n) :
    (n/2)*(Nat.log2 n+1) ≤ d+2 := by
  have hne : n ≠ 0 := by omega
  have hlog := (Nat.log2_eq_iff hne).mp rfl
  have hlogpos : 1 ≤ Nat.log2 n := by
    by_cases hz : Nat.log2 n = 0
    · have hpown : 2^(Nat.log2 n+1) = 2 := by simp [hz]
      have hupper := hlog.2
      rw [hpown] at hupper
      omega
    · omega
  have hp : 2^((Nat.log2 n-1)+1) ≤ n := by
    have heq : (Nat.log2 n-1)+1=Nat.log2 n := by omega
    rw [heq]
    exact hlog.1
  have hh := original_iterate_superlinear d n (Nat.log2 n-1) hr hp
  have heq : (Nat.log2 n-1)+2=Nat.log2 n+1 := by omega
  rw [heq] at hh
  exact hh

/-- Certified finite forward-check cutoff for any prescribed target. The
    parameter M can be selected from the target's binary length. -/
def timeFuel (d M : Nat) : Nat :=
  max (2^(M+1)) (2*((d+2)/(M+2))+2)

/-- A source-authentic complete finite test of each fixed blank-root target
    with a logarithmically improved time cutoff. -/
theorem genuine_root_iff_bounded (d M : Nat) :
    ReachN d ↔
      ∃ n, n < timeFuel d M ∧ sourceRun n = some (.N d) := by
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n,?_,?_⟩
    · rcases original_iterate_time_upper d n M hn with hsmall|hlarge
      · exact Nat.lt_of_lt_of_le hsmall (Nat.le_max_left _ _)
      · have hh : n < 2*((d+2)/(M+2))+2 := by omega
        exact Nat.lt_of_lt_of_le hh (Nat.le_max_right _ _)
    · rw [sourceRun_eq_iter]
      exact hn
  · rintro ⟨n,_,hn⟩
    refine ⟨n,?_⟩
    rw [←sourceRun_eq_iter]
    exact hn

/-- A concrete optimized fuel chosen as half the binary logarithm of the
    target, balancing the head and tail terms. -/
def optimizedFuel (d : Nat) : Nat :=
  timeFuel d (Nat.log2 (d+2)/2)

theorem genuine_root_iff_optimized (d : Nat) :
    ReachN d ↔ ∃ n, n < optimizedFuel d ∧ sourceRun n = some (.N d) := by
  exact genuine_root_iff_bounded d (Nat.log2 (d+2)/2)

#print axioms BB6.Agent20.SpaceNeedleGrowth.original_iterate_time_upper
#print axioms BB6.Agent20.SpaceNeedleGrowth.original_iterate_log_growth
#print axioms BB6.Agent20.SpaceNeedleGrowth.genuine_root_iff_bounded
#print axioms BB6.Agent20.SpaceNeedleGrowth.genuine_root_iff_optimized
end BB6.Agent20.SpaceNeedleGrowth
