import CancellationDepthTwo
import NeedleCancellationFour
import Lean.Elab.Tactic.Omega

namespace BB6.Agent48.SpaceNeedleDepthTwo
open BB6.Agent48.SpaceNeedle
open BusyBeaver
open BB6.Agent47NeedleCancellationFour
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open NeedleCancelMod35

private theorem source_step_formula (q v : Nat) :
    highLevelNext (.N (oddTower q v)) =
      some (.N (oddTower q v+v+3*(q+1))) := by
  change scanEven (oddTower q v) 0 = _
  simpa using scan_oddTower q v 0

private theorem source_four_target (r q : Nat) (hr : 1≤r)
    (h : highLevelNext (.N (oddTower q 4)) =
      some (.N (oddTower (CancellationConstructive.feederQ r)
        (CancellationTerminalConstructive.feederV r)))) :
    sourceB r=35*q+55 := by
  have hstep := source_step_formula q 4
  rw [hstep] at h
  simp only [Option.some.injEq, HighLevelState.N.injEq] at h
  have hfeed := sourceB_is_original_feeder r hr
  have hfour : oddTower q 4+2=16*(2*q+3) := by
    simpa using oddTower_factor q 4
  omega

private theorem source_zero_target (p q : Nat)
    (h : highLevelNext (.N (oddTower p 0)) = some (.N (oddTower q 4))) :
    5*p+4=oddTower q 4 := by
  have hstep := source_step_formula p 0
  rw [hstep] at h
  simp only [Option.some.injEq, HighLevelState.N.injEq] at h
  have hzero : oddTower p 0+2=2*p+3 := by
    simpa using oddTower_factor p 0
  omega

/-- For every positive cancellation feeder index r, an exact original
    high-level two-edge predecessor chain of valuations 0 and 4 exists
    if and only if r is 4 modulo 30.  Both edges are source transitions;
    their states are not asserted to be reachable from the blank tape. -/
theorem cancellation_zero_four_chain_iff (r : Nat) (hr : 1≤r) :
    (∃ p0 p4 : Nat,
      highLevelNext (.N (oddTower p0 0)) = some (.N (oddTower p4 4)) ∧
      highLevelNext (.N (oddTower p4 4)) =
        some (.N (oddTower (CancellationConstructive.feederQ r)
          (CancellationTerminalConstructive.feederV r)))) ↔ r%30=4 := by
  constructor
  · rintro ⟨p0,p4,hzero,hfour⟩
    have hb := source_four_target r p4 hr hfour
    have hz := source_zero_target p0 p4 hzero
    have hfourfactor : oddTower p4 4+2=16*(2*p4+3) := by
      simpa using oddTower_factor p4 4
    have hmod : sourceB r%175=20 := by omega
    exact (NeedleCancelDepthTwo.cancellation_four_then_zero_residue r hr).mp hmod
  · intro hr30
    have hr3 : r%3=1 := by omega
    have hrep : r=3*(r/3)+1 := by omega
    obtain ⟨p4,hfour⟩ := infinite_cancellation_four_parent (r/3)
    have hfour' : highLevelNext (.N (oddTower p4 4)) =
      some (.N (oddTower (CancellationConstructive.feederQ r)
        (CancellationTerminalConstructive.feederV r))) := by
      simpa [←hrep] using hfour
    have hb := source_four_target r p4 hr hfour'
    have hmod : sourceB r%175=20 :=
      (NeedleCancelDepthTwo.cancellation_four_then_zero_residue r hr).mpr hr30
    have hp4 : p4%5=4 := by omega
    let p0 := (32*p4+42)/5
    have hz : 5*p0+4=oddTower p4 4 := by
      have hfourfactor : oddTower p4 4+2=16*(2*p4+3) := by
        simpa using oddTower_factor p4 4
      dsimp [p0]
      omega
    have hzero : oddTower p0 0+2=2*p0+3 := by
      simpa using oddTower_factor p0 0
    have hsource : highLevelNext (.N (oddTower p0 0)) =
        some (.N (oddTower p4 4)) := by
      have hstep := source_step_formula p0 0
      have heq : oddTower p0 0+0+3*(p0+1)=oddTower p4 4 := by omega
      rw [heq] at hstep
      exact hstep
    exact ⟨p0,p4,hsource,hfour'⟩

#print axioms cancellation_zero_four_chain_iff
end BB6.Agent48.SpaceNeedleDepthTwo
