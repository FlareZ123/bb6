import CancellationDepthThree
import CancellationDepthTwoSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent48.SpaceNeedleDepthThree
open BB6.Agent48.SpaceNeedle
open BusyBeaver
open BB6.Agent47NeedleCancellationFour
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open NeedleCancelMod35

private theorem step_formula (q v : Nat) :
    highLevelNext (.N (oddTower q v)) =
      some (.N (oddTower q v+v+3*(q+1))) := by
  change scanEven (oddTower q v) 0 = _
  simpa using scan_oddTower q v 0

private theorem source_four_target (r q : Nat) (hr : 1≤r)
    (h : highLevelNext (.N (oddTower q 4)) =
      some (.N (oddTower (CancellationConstructive.feederQ r)
        (CancellationTerminalConstructive.feederV r)))) :
    sourceB r=35*q+55 := by
  have hstep := step_formula q 4
  rw [hstep] at h
  simp only [Option.some.injEq, HighLevelState.N.injEq] at h
  have hfeed := sourceB_is_original_feeder r hr
  have hfour : oddTower q 4+2=16*(2*q+3) := by
    simpa using oddTower_factor q 4
  omega

private theorem source_zero_target (p q : Nat)
    (h : highLevelNext (.N (oddTower p 0)) = some (.N (oddTower q 4))) :
    5*p+4=oddTower q 4 := by
  have hstep := step_formula p 0
  rw [hstep] at h
  simp only [Option.some.injEq, HighLevelState.N.injEq] at h
  have hzero : oddTower p 0+2=2*p+3 := by
    simpa using oddTower_factor p 0
  omega

private theorem source_one_target (p q : Nat)
    (h : highLevelNext (.N (oddTower p 1)) = some (.N (oddTower q 0))) :
    7*p+8=oddTower q 0 := by
  have hstep := step_formula p 1
  rw [hstep] at h
  simp only [Option.some.injEq, HighLevelState.N.injEq] at h
  have hone : oddTower p 1+2=2*(2*p+3) := by
    simpa using oddTower_factor p 1
  omega

/-- Complete original-source classification of the three incoming edges
    with valuations 1, 0, and 4, in that chronological order. -/
theorem cancellation_one_zero_four_chain_iff (r : Nat) (hr : 1≤r) :
    (∃ p1 p0 p4 : Nat,
      highLevelNext (.N (oddTower p1 1)) = some (.N (oddTower p0 0)) ∧
      highLevelNext (.N (oddTower p0 0)) = some (.N (oddTower p4 4)) ∧
      highLevelNext (.N (oddTower p4 4)) =
        some (.N (oddTower (CancellationConstructive.feederQ r)
          (CancellationTerminalConstructive.feederV r)))) ↔ r%210=4 := by
  constructor
  · rintro ⟨p1,p0,p4,h10,h04,h4⟩
    have hB := source_four_target r p4 hr h4
    have hZ := source_zero_target p0 p4 h04
    have hO := source_one_target p1 p0 h10
    have hfact4 : oddTower p4 4+2=16*(2*p4+3) := by
      simpa using oddTower_factor p4 4
    have hfact0 : oddTower p0 0+2=2*p0+3 := by
      simpa using oddTower_factor p0 0
    have hBmod : sourceB r%1225=545 := by omega
    exact (NeedleCancelDepthThree.cancellation_one_zero_four_residue r hr).mp hBmod
  · intro h210
    have h30 : r%30=4 := by omega
    obtain ⟨p0,p4,h04,h4⟩ :=
      (BB6.Agent48.SpaceNeedleDepthTwo.cancellation_zero_four_chain_iff r hr).mpr h30
    have hB := source_four_target r p4 hr h4
    have hZ := source_zero_target p0 p4 h04
    have hfact4 : oddTower p4 4+2=16*(2*p4+3) := by
      simpa using oddTower_factor p4 4
    have hBmod : sourceB r%1225=545 :=
      (NeedleCancelDepthThree.cancellation_one_zero_four_residue r hr).mpr h210
    have hp0mod : p0%7=0 := by omega
    have hp0large : 7≤p0 := by omega
    let p1 := (2*p0-7)/7
    have hfact0 : oddTower p0 0+2=2*p0+3 := by
      simpa using oddTower_factor p0 0
    have hfact1 : oddTower p1 1+2=2*(2*p1+3) := by
      simpa using oddTower_factor p1 1
    have hp1eq : 7*p1+7=2*p0 := by
      dsimp [p1]
      omega
    have hnext : oddTower p1 1+1+3*(p1+1)=oddTower p0 0 := by
      omega
    have hstep := step_formula p1 1
    rw [hnext] at hstep
    exact ⟨p1,p0,p4,hstep,h04,h4⟩

#print axioms cancellation_one_zero_four_chain_iff
end BB6.Agent48.SpaceNeedleDepthThree
