import CancellationThreeSource
import CancellationFiveSubfamily
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46NeedleThree
open BB6.Agent48.SpaceNeedle
open BB6.Agent47NeedleCancellationFour
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

/-- For every t, the same cancellation feeder admits a valuation-five
    predecessor, supplementing its valuation-three and valuation-four edges. -/
theorem sourceB_parent5 (t : Nat) :
    ∃ q5 : Nat, sourceB (214+495*t)=67*q5+104 := by
  have hd := CancellationFive.val_five_subfamily t
  rw [←double_sourceB (214+495*t)] at hd
  have hsize := sourceB_ge55 (214+495*t) (by omega)
  have hz : (2*sourceB (214+495*t)+3-10)%67=0 :=
    Nat.mod_eq_zero_of_dvd hd
  have hmod : sourceB (214+495*t)%67=37 := by omega
  refine ⟨(sourceB (214+495*t)-104)/67,?_⟩
  omega

/-- Original, unchanged Space Needle high-level map has all three
    distinct synthetic immediate predecessors for every r=214+495t. -/
theorem infinite_three_predecessors (t : Nat) :
    ∃ q3 q4 q5 : Nat,
      highLevelNext (.N (oddTower q3 3)) =
        some (.N (oddTower (CancellationConstructive.feederQ (214+495*t))
          (CancellationTerminalConstructive.feederV (214+495*t)))) ∧
      highLevelNext (.N (oddTower q4 4)) =
        some (.N (oddTower (CancellationConstructive.feederQ (214+495*t))
          (CancellationTerminalConstructive.feederV (214+495*t)))) ∧
      highLevelNext (.N (oddTower q5 5)) =
        some (.N (oddTower (CancellationConstructive.feederQ (214+495*t))
          (CancellationTerminalConstructive.feederV (214+495*t)))) ∧
      oddTower q3 3 ≠ oddTower q4 4 ∧
      oddTower q3 3 ≠ oddTower q5 5 ∧
      oddTower q4 4 ≠ oddTower q5 5 := by
  obtain ⟨q3,q4,h3,h4,hne34⟩ := infinite_two_predecessors (23+55*t)
  have he : 9*(23+55*t)+7=214+495*t := by omega
  rw [he] at h3 h4
  obtain ⟨q5,hq5⟩ := sourceB_parent5 t
  have hfeed := sourceB_is_original_feeder (214+495*t) (by omega)
  have hfactor5 := oddTower_factor q5 5
  have h5 :
      highLevelNext (.N (oddTower q5 5)) =
        some (.N (oddTower (CancellationConstructive.feederQ (214+495*t))
          (CancellationTerminalConstructive.feederV (214+495*t)))) := by
    apply (highLevelNext_iff_oddTower _ _).mpr
    refine ⟨q5,5,rfl,?_⟩
    have h32 : (2:Nat)^5=32 := by decide
    rw [h32] at hfactor5
    omega
  have hfactor3 := oddTower_factor q3 3
  have hfactor4 := oddTower_factor q4 4
  have h8 : (2:Nat)^3=8 := by decide
  have h16 : (2:Nat)^4=16 := by decide
  have h32 : (2:Nat)^5=32 := by decide
  rw [h8] at hfactor3
  rw [h16] at hfactor4
  rw [h32] at hfactor5
  have hne35 : oddTower q3 3 ≠ oddTower q5 5 := by
    intro h
    rw [h] at hfactor3
    omega
  have hne45 : oddTower q4 4 ≠ oddTower q5 5 := by
    intro h
    rw [h] at hfactor4
    omega
  exact ⟨q3,q4,q5,h3,h4,h5,hne34,hne35,hne45⟩

#print axioms sourceB_parent5
#print axioms infinite_three_predecessors
end BB6.Agent46NeedleThree
