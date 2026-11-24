
import NeedleCubicFuel
import NeedleGrowthScan
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46.SpaceNeedleCubic
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open BB6.Agent20.SpaceNeedleGrowthScan
open BB6.Agent20.SpaceNeedleGrowth

/-- Four original-source edges satisfy the stronger cube gain. -/
theorem original_four_step_cube_gain (d e f g h : Nat)
    (hde : highLevelNext (.N d)=some (.N e))
    (hef : highLevelNext (.N e)=some (.N f))
    (hfg : highLevelNext (.N f)=some (.N g))
    (hgh : highLevelNext (.N g)=some (.N h)) :
    (d+2)^2≤64*(Nat.log2 (d+2)+1)*((h+2)-(d+2))^3 := by
  exact NeedleFourStep.four_step_bitlength_gain
    (original_edge d e hde) (original_edge e f hef)
    (original_edge f g hfg) (original_edge g h hgh)

private def rootRun (n : Nat) : Option HighLevelState :=
  runFrom (some highLevelStart) n

private theorem rootRun_iter (n : Nat) :
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
    ∀ i, i≤n → (∃ d, rootRun n=some (.N d)) →
      ∃ d, rootRun i=some (.N d) := by
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
    · obtain ⟨d,hdn⟩ := hd
      have hprev : ∃ p, rootRun n=some (.N p) := by
        change (rootRun n).bind highLevelNext=some (.N d) at hdn
        cases hr : rootRun n with
        | none => simp [hr] at hdn
        | some st =>
          cases st with
          | N p => exact ⟨p,rfl⟩
      exact ih i (by omega) hprev

private def counterAt (i : Nat) : Nat :=
  match rootRun i with
  | some (.N d) => d
  | none => 0

private theorem counterAt_spec (i d : Nat)
    (hr : rootRun i=some (.N d)) : counterAt i=d := by
  simp [counterAt,hr]

private theorem original_root_prefix (d n : Nat)
    (hr : rootRun n=some (.N d)) :
    NeedleFourStep.Prefix (fun i => counterAt i+2) n := by
  intro i hi
  obtain ⟨p,hp⟩ := rootRun_prefix n i (by omega) ⟨d,hr⟩
  obtain ⟨e,he⟩ := rootRun_prefix n (i+1) (by omega) ⟨d,hr⟩
  have hs : highLevelNext (.N p)=some (.N e) := by
    have hh := he
    change (rootRun i).bind highLevelNext=some (.N e) at hh
    rw [hp] at hh
    simpa using hh
  have hh : NeedleFourStep.Edge (p+2) (e+2) := original_edge p e hs
  simpa [counterAt_spec i p hp, counterAt_spec (i+1) e he] using hh

/-- Every successful genuine blank-root trace reaching d has length
O((d log d)^(1/3)) in original high-level transitions. -/
theorem original_iterate_cube_bound (d n : Nat)
    (hr : Nat.iterate (fun z : Option HighLevelState => z.bind highLevelNext)
      n (some highLevelStart)=some (.N d)) :
    n<NeedleFourStep.cubeFuel d := by
  have hrr : rootRun n=some (.N d) := by rwa [rootRun_iter]
  have hp := original_root_prefix d n hrr
  have hb : 1≤counterAt 0+2 := by omega
  exact NeedleFourStep.prefix_cube_fuel (fun i => counterAt i+2) n d hp hb
    (by rw [counterAt_spec n d hrr])

/-- Exact executable single-pass root membership with the stronger bound. -/
def cubeScan (d : Nat) : Bool :=
  scan d (NeedleFourStep.cubeFuel d) (some highLevelStart)

theorem cubeScan_spec (d : Nat) : cubeScan d=true ↔ ReachN d := by
  rw [cubeScan,scan_spec]
  constructor
  · rintro ⟨n,_,hn⟩
    refine ⟨n,?_⟩
    change Nat.iterate (fun z : Option HighLevelState => z.bind highLevelNext)
      n (some highLevelStart)=some (.N d)
    rw [←rootRun_iter]
    exact hn
  · rintro ⟨n,hn⟩
    refine ⟨n,original_iterate_cube_bound d n hn,?_⟩
    change rootRun n=some (.N d)
    rw [rootRun_iter]
    exact hn

#print axioms original_four_step_cube_gain
#print axioms original_iterate_cube_bound
#print axioms cubeScan_spec
end BB6.Agent46.SpaceNeedleCubic
