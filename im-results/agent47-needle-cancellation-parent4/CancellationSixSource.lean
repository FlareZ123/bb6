import CancellationFiveSource
import CancellationSixArithmetic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent47NeedleSix
open BB6.Agent48.SpaceNeedle
open BB6.Agent47NeedleCancellationFour
open BB6.Agent46NeedleThree
open NeedleCancelMod35
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

private theorem sourceB_ge201 (r : Nat) (hr : 1 ≤ r) : 201 ≤ sourceB r := by
  have hv : 6 ≤ v r := by
    have hp : 9 ≤ 9^r := by
      have h := Nat.pow_le_pow_right (by decide : 0 < (9:Nat)) hr
      simpa using h
    dsimp [v]
    omega
  have hp : 64 ≤ 2^(v r) := Nat.pow_le_pow_right (by decide) hv
  have hx : 128 ≤ xb r := by
    unfold xb
    exact Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega)
  have hg : 1 ≤ geo ((xb r)^2) 9 r :=
    geo_pos ((xb r)^2) 9 r (by decide) hr
  have hsub : 125 ≤ xb r-3 := by omega
  have hproduct : 64*125 ≤ 2^(v r)*(xb r-3) :=
    Nat.mul_le_mul hp hsub
  have hfull : (64*125)*1 ≤
      (2^(v r)*(xb r-3))*geo ((xb r)^2) 9 r :=
    Nat.mul_le_mul hproduct hg
  dsimp [sourceB]
  omega

/-- Genuine high-level valuation-six inverse is present on an unbounded
    subprogression of the existing three-parent cancellation family. -/
theorem sourceB_parent6 (t : Nat) :
    ∃ q6 : Nat, sourceB (64069+1685970*t)=131*q6+201 := by
  let r := 64069+1685970*t
  have hmod : sourceB r %131=70 := CancellationSix.sourceB_mod131 t
  have hsize : 201 ≤ sourceB r := sourceB_ge201 r (by dsimp [r]; omega)
  refine ⟨(sourceB r-201)/131, ?_⟩
  omega

/-- The real pinned Space Needle source map has distinct immediate parents
    at valuations 3, 4, 5 and 6 for every member of the progression. -/
theorem infinite_four_predecessors (t : Nat) :
    ∃ q3 q4 q5 q6 : Nat,
      highLevelNext (.N (oddTower q3 3)) =
        some (.N (oddTower (CancellationConstructive.feederQ (64069+1685970*t))
          (CancellationTerminalConstructive.feederV (64069+1685970*t)))) ∧
      highLevelNext (.N (oddTower q4 4)) =
        some (.N (oddTower (CancellationConstructive.feederQ (64069+1685970*t))
          (CancellationTerminalConstructive.feederV (64069+1685970*t)))) ∧
      highLevelNext (.N (oddTower q5 5)) =
        some (.N (oddTower (CancellationConstructive.feederQ (64069+1685970*t))
          (CancellationTerminalConstructive.feederV (64069+1685970*t)))) ∧
      highLevelNext (.N (oddTower q6 6)) =
        some (.N (oddTower (CancellationConstructive.feederQ (64069+1685970*t))
          (CancellationTerminalConstructive.feederV (64069+1685970*t)))) ∧
      oddTower q3 3 ≠ oddTower q4 4 ∧
      oddTower q3 3 ≠ oddTower q5 5 ∧
      oddTower q3 3 ≠ oddTower q6 6 ∧
      oddTower q4 4 ≠ oddTower q5 5 ∧
      oddTower q4 4 ≠ oddTower q6 6 ∧
      oddTower q5 5 ≠ oddTower q6 6 := by
  obtain ⟨q3,q4,q5,h3,h4,h5,hne34,hne35,hne45⟩ :=
    infinite_three_predecessors (129+3406*t)
  have he : 214+495*(129+3406*t)=64069+1685970*t := by omega
  rw [he] at h3 h4 h5
  obtain ⟨q6,hq6⟩ := sourceB_parent6 t
  have hfeed := sourceB_is_original_feeder (64069+1685970*t) (by omega)
  have hfactor6 := oddTower_factor q6 6
  have h6 :
      highLevelNext (.N (oddTower q6 6)) =
        some (.N (oddTower (CancellationConstructive.feederQ (64069+1685970*t))
          (CancellationTerminalConstructive.feederV (64069+1685970*t)))) := by
    apply (highLevelNext_iff_oddTower _ _).mpr
    refine ⟨q6,6,rfl,?_⟩
    have h64 : (2:Nat)^6=64 := by decide
    rw [h64] at hfactor6
    omega
  have hfactor3 := oddTower_factor q3 3
  have hfactor4 := oddTower_factor q4 4
  have hfactor5 := oddTower_factor q5 5
  have h8 : (2:Nat)^3=8 := by decide
  have h16 : (2:Nat)^4=16 := by decide
  have h32 : (2:Nat)^5=32 := by decide
  have h64 : (2:Nat)^6=64 := by decide
  rw [h8] at hfactor3
  rw [h16] at hfactor4
  rw [h32] at hfactor5
  rw [h64] at hfactor6
  have hne36 : oddTower q3 3 ≠ oddTower q6 6 := by
    intro h
    rw [h] at hfactor3
    omega
  have hne46 : oddTower q4 4 ≠ oddTower q6 6 := by
    intro h
    rw [h] at hfactor4
    omega
  have hne56 : oddTower q5 5 ≠ oddTower q6 6 := by
    intro h
    rw [h] at hfactor5
    omega
  exact ⟨q3,q4,q5,q6,h3,h4,h5,h6,hne34,hne35,hne36,hne45,hne46,hne56⟩

#print axioms sourceB_parent6
#print axioms infinite_four_predecessors
end BB6.Agent47NeedleSix
