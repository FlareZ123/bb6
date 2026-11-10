import NeedleQuadratic
import NeedleGrowthScan
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20.SpaceNeedleQuadratic
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open BB6.Agent20.SpaceNeedleGrowthScan
open BB6.Agent20.SpaceNeedleGrowth

/-- Any two consecutive genuine source edges have square-root-scale gain. -/
theorem original_two_step_square_gain (d e f : Nat)
    (hde : highLevelNext (.N d) = some (.N e))
    (hef : highLevelNext (.N e) = some (.N f)) :
    d+2 ≤ ((f+2)-(d+2))^2 := by
  exact NeedleGrowth.two_step_square_gain
    (original_edge d e hde) (original_edge e f hef)

private def rootRun (i : Nat) : Option HighLevelState :=
  runFrom (some highLevelStart) i

private theorem rootRun_eq_iter (n : Nat) :
    rootRun n = Nat.iterate
      (fun z : Option HighLevelState => z.bind highLevelNext)
      n (some highLevelStart) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (rootRun n).bind highLevelNext = _
      rw [ih]
      rw [Nat.add_comm n 1, Function.iterate_add_apply]
      rfl

private theorem rootRun_prefix (n : Nat) :
    ∀ i, i ≤ n → (∃ d, rootRun n = some (.N d)) →
      ∃ d, rootRun i = some (.N d) := by
  induction n with
  | zero =>
      intro i hi hd
      have heq : i=0 := by omega
      subst i
      exact hd
  | succ n ih =>
      intro i hi hd
      by_cases heq : i=n+1
      · simpa [heq] using hd
      · have hi' : i≤n := by omega
        obtain ⟨d,hdn⟩ := hd
        have hprev : ∃ p, rootRun n = some (.N p) := by
          change (rootRun n).bind highLevelNext = some (.N d) at hdn
          cases hr : rootRun n with
          | none => simp [hr] at hdn
          | some state =>
              cases state with
              | N p => exact ⟨p,rfl⟩
        exact ih i hi' hprev

private def counterAt (i : Nat) : Nat :=
  match rootRun i with
  | some (.N d) => d
  | none => 0

private theorem counterAt_spec (i d : Nat)
    (h : rootRun i = some (.N d)) : counterAt i = d := by
  simp [counterAt,h]

private theorem original_root_prefix (d n : Nat)
    (hr : rootRun n = some (.N d)) :
    NeedleGrowth.Prefix (fun i => counterAt i + 2) n := by
  intro i hi
  obtain ⟨p,hp⟩ := rootRun_prefix n i (by omega) ⟨d,hr⟩
  obtain ⟨e,he⟩ := rootRun_prefix n (i+1) (by omega) ⟨d,hr⟩
  have hstep : highLevelNext (.N p) = some (.N e) := by
    have hh := he
    change (rootRun i).bind highLevelNext = some (.N e) at hh
    rw [hp] at hh
    simpa using hh
  have hh := original_edge p e hstep
  simpa [counterAt_spec i p hp, counterAt_spec (i+1) e he] using hh

/-- Quadratic growth for each finite successful original blank-root trace. -/
theorem original_iterate_quadratic (d n : Nat)
    (hr : Nat.iterate (fun z : Option HighLevelState => z.bind highLevelNext)
        n (some highLevelStart) = some (.N d)) :
    (n/4+1)^2+1 ≤ d+2 := by
  have hrr : rootRun n = some (.N d) := by
    rw [rootRun_eq_iter]
    exact hr
  have hp := original_root_prefix d n hrr
  have hbase : 2 ≤ counterAt 0+2 := by omega
  have hquad := NeedleGrowth.prefix_quadratic_index
    (fun i => counterAt i+2) n n hp hbase (by omega)
  rw [counterAt_spec n d hrr] at hquad
  exact hquad

/-- Original blank-root return times have a rigorous square-root cutoff. -/
def sqrtFuel (d : Nat) : Nat := 4*(Nat.sqrt (d+1)+1)

theorem original_iterate_sqrt_bound (d n : Nat)
    (hr : Nat.iterate (fun z : Option HighLevelState => z.bind highLevelNext)
        n (some highLevelStart) = some (.N d)) :
    n < sqrtFuel d := by
  exact NeedleGrowth.quadratic_index_sqrt_bound d n
    (original_iterate_quadratic d n hr)

theorem genuine_root_iff_sqrt_fuel (d : Nat) :
    ReachN d ↔
    ∃ n, n<sqrtFuel d ∧ rootRun n = some (.N d) := by
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨n,original_iterate_sqrt_bound d n hn, by rw [rootRun_eq_iter]; exact hn⟩
  · rintro ⟨n,_,hn⟩
    refine ⟨n,?_⟩
    change Nat.iterate (fun z : Option HighLevelState => z.bind highLevelNext)
      n (some highLevelStart) = some (.N d)
    rw [←rootRun_eq_iter]
    exact hn

/-- Executable exact original-source Boolean root membership with
    a finite O(sqrt(d)) high-level step cutoff. -/
def sqrtScan (d : Nat) : Bool :=
  scan d (sqrtFuel d) (some highLevelStart)

theorem sqrtScan_spec (d : Nat) :
    sqrtScan d = true ↔ ReachN d := by
  rw [sqrtScan, scan_spec]
  constructor
  · rintro ⟨n,hn,hr⟩
    refine ⟨n,?_⟩
    change Nat.iterate (fun z : Option HighLevelState => z.bind highLevelNext)
      n (some highLevelStart) = some (.N d)
    rw [←rootRun_eq_iter]
    exact hr
  · rintro ⟨n,hn⟩
    refine ⟨n,original_iterate_sqrt_bound d n hn,?_⟩
    change rootRun n = some (.N d)
    rw [rootRun_eq_iter]
    exact hn

#print axioms BB6.Agent20.SpaceNeedleQuadratic.original_two_step_square_gain
#print axioms BB6.Agent20.SpaceNeedleQuadratic.original_iterate_quadratic
#print axioms BB6.Agent20.SpaceNeedleQuadratic.genuine_root_iff_sqrt_fuel
#print axioms BB6.Agent20.SpaceNeedleQuadratic.sqrtScan_spec
end BB6.Agent20.SpaceNeedleQuadratic
