import CancellationSixSource
import CancellationElevenArithmetic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent47NeedleEleven
open BB6.Agent48.SpaceNeedle
open BB6.Agent47NeedleCancellationFour
open BB6.Agent47NeedleSix
open NeedleCancelMod35
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

/-- A fifth valuation arm is arithmetically permitted at every index in
    the sharpened infinite cancellation progression. -/
theorem sourceB_parent11 (t:Nat) :
    ∃ q11 : Nat,
      sourceB (CancellationEleven.idx t)=4099*q11+6158 := by
  let r:=CancellationEleven.idx t
  have hmod : sourceB r%4099=2059 := CancellationEleven.sourceB_mod4099 t
  have hbig : 6158≤sourceB r := by
    have h := sourceB_ge8000 r (by dsimp [r,CancellationEleven.idx]; omega)
    omega
  refine ⟨(sourceB r-6158)/4099, ?_⟩
  change sourceB r = 4099*((sourceB r-6158)/4099)+6158
  omega

/-- Five mutually distinct actual incoming high-level source transitions
    into an infinite subfamily of the genuine cancellation terminal feeders.
    These are arbitrary-source edges; the blank-root question remains open. -/
theorem infinite_five_predecessors (t:Nat) :
    ∃ q3 q4 q5 q6 q11 : Nat,
      highLevelNext (.N (oddTower q3 3)) =
        some (.N (oddTower (CancellationConstructive.feederQ (CancellationEleven.idx t))
          (CancellationTerminalConstructive.feederV (CancellationEleven.idx t)))) ∧
      highLevelNext (.N (oddTower q4 4)) =
        some (.N (oddTower (CancellationConstructive.feederQ (CancellationEleven.idx t))
          (CancellationTerminalConstructive.feederV (CancellationEleven.idx t)))) ∧
      highLevelNext (.N (oddTower q5 5)) =
        some (.N (oddTower (CancellationConstructive.feederQ (CancellationEleven.idx t))
          (CancellationTerminalConstructive.feederV (CancellationEleven.idx t)))) ∧
      highLevelNext (.N (oddTower q6 6)) =
        some (.N (oddTower (CancellationConstructive.feederQ (CancellationEleven.idx t))
          (CancellationTerminalConstructive.feederV (CancellationEleven.idx t)))) ∧
      highLevelNext (.N (oddTower q11 11)) =
        some (.N (oddTower (CancellationConstructive.feederQ (CancellationEleven.idx t))
          (CancellationTerminalConstructive.feederV (CancellationEleven.idx t)))) ∧
      oddTower q3 3 ≠ oddTower q4 4 ∧
      oddTower q3 3 ≠ oddTower q5 5 ∧
      oddTower q3 3 ≠ oddTower q6 6 ∧
      oddTower q3 3 ≠ oddTower q11 11 ∧
      oddTower q4 4 ≠ oddTower q5 5 ∧
      oddTower q4 4 ≠ oddTower q6 6 ∧
      oddTower q4 4 ≠ oddTower q11 11 ∧
      oddTower q5 5 ≠ oddTower q6 6 ∧
      oddTower q5 5 ≠ oddTower q11 11 ∧
      oddTower q6 6 ≠ oddTower q11 11 := by
  obtain ⟨q3,q4,q5,q6,h3,h4,h5,h6,hne34,hne35,hne36,hne45,hne46,hne56⟩ :=
    infinite_four_predecessors (2463+21173*t)
  have he : 64069+1685970*(2463+21173*t) = CancellationEleven.idx t := by
    dsimp [CancellationEleven.idx]
    omega
  rw [he] at h3 h4 h5 h6
  obtain ⟨q11,hq11⟩ := sourceB_parent11 t
  have hfeed := sourceB_is_original_feeder (CancellationEleven.idx t) (by
    dsimp [CancellationEleven.idx]; omega)
  have hfactor11 := oddTower_factor q11 11
  have h11 :
      highLevelNext (.N (oddTower q11 11)) =
        some (.N (oddTower (CancellationConstructive.feederQ (CancellationEleven.idx t))
          (CancellationTerminalConstructive.feederV (CancellationEleven.idx t)))) := by
    apply (highLevelNext_iff_oddTower _ _).mpr
    refine ⟨q11,11,rfl,?_⟩
    have h2048 : (2:Nat)^11=2048 := by decide
    rw [h2048] at hfactor11
    omega
  have hfactor3 := oddTower_factor q3 3
  have hfactor4 := oddTower_factor q4 4
  have hfactor5 := oddTower_factor q5 5
  have hfactor6 := oddTower_factor q6 6
  have h8 : (2:Nat)^3=8 := by decide
  have h16 : (2:Nat)^4=16 := by decide
  have h32 : (2:Nat)^5=32 := by decide
  have h64 : (2:Nat)^6=64 := by decide
  have h2048 : (2:Nat)^11=2048 := by decide
  rw [h8] at hfactor3
  rw [h16] at hfactor4
  rw [h32] at hfactor5
  rw [h64] at hfactor6
  rw [h2048] at hfactor11
  have hne311 : oddTower q3 3 ≠ oddTower q11 11 := by
    intro h
    rw [h] at hfactor3
    omega
  have hne411 : oddTower q4 4 ≠ oddTower q11 11 := by
    intro h
    rw [h] at hfactor4
    omega
  have hne511 : oddTower q5 5 ≠ oddTower q11 11 := by
    intro h
    rw [h] at hfactor5
    omega
  have hne611 : oddTower q6 6 ≠ oddTower q11 11 := by
    intro h
    rw [h] at hfactor6
    omega
  exact ⟨q3,q4,q5,q6,q11,h3,h4,h5,h6,h11,
    hne34,hne35,hne36,hne311,hne45,hne46,hne411,
    hne56,hne511,hne611⟩

#print axioms sourceB_parent11
#print axioms infinite_five_predecessors
end BB6.Agent47NeedleEleven
