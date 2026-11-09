import NeedleCancellationFour
import CancellationThreeArithmetic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46NeedleThree
open BB6.Agent48.SpaceNeedle
open BB6.Agent47NeedleCancellationFour
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open CancellationNat CancellationGap

/-- The source-shaped shifted feeder has twice the cancellation polynomial mass. -/
theorem double_sourceB (r : Nat) :
    2*sourceB r = 2^(valuationA r)*P (2^(valuationA r)) r := by
  rw [sourceB_eq_P, valuationA_eq_v_succ, Nat.pow_succ]
  ac_rfl

/-- Exact valuation-three congruence for the original prepared feeder counter. -/
theorem sourceB_mod19_iff (r : Nat) (hr : 1≤r) :
    sourceB r %19=11 ↔ r%9=7 := by
  have hval := CancellationThree.val_three_iff r hr
  rw [←double_sourceB r] at hval
  have hlarge : 55≤sourceB r := sourceB_ge55 r hr
  have hdiv : (19 ∣ (2*sourceB r+3-2*3)) ↔ sourceB r%19=11 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  exact hdiv.symm.trans hval

/-- Every r=9t+7 has a legal valuation-three predecessor, and no
    other positive cancellation index has a valuation-three predecessor. -/
theorem sourceB_parent3_iff (r : Nat) (hr : 1≤r) :
    (∃ q:Nat, sourceB r=19*q+30) ↔ r%9=7 := by
  rw [←sourceB_mod19_iff r hr]
  constructor
  · rintro ⟨q,hq⟩
    rw [hq]
    omega
  · intro hr19
    have hsize := sourceB_ge55 r hr
    refine ⟨(sourceB r-30)/19,?_⟩
    omega

/-- Original-source high-level transition classification. Prepared incoming
    edges are not evidence of genuine blank-root reachability. -/
theorem cancellation_three_parent_iff (r : Nat) (hr : 1≤r) :
    (∃ q : Nat,
      highLevelNext (.N (oddTower q 3)) =
        some (.N (oddTower
          (CancellationConstructive.feederQ r)
          (CancellationTerminalConstructive.feederV r)))) ↔
      r%9=7 := by
  constructor
  · rintro ⟨q,hstep⟩
    have hstepFormula :
        highLevelNext (.N (oddTower q 3)) =
          some (.N (oddTower q 3+3+3*(q+1))) := by
      change scanEven (oddTower q 3) 0 = _
      simpa using scan_oddTower q 3 0
    rw [hstepFormula] at hstep
    simp only [Option.some.injEq, HighLevelState.N.injEq] at hstep
    have hfeed := sourceB_is_original_feeder r hr
    have hq3 : oddTower q 3+2=8*(2*q+3) := by
      simpa using oddTower_factor q 3
    have hb : sourceB r=19*q+30 := by omega
    exact (sourceB_parent3_iff r hr).mp ⟨q,hb⟩
  · intro hm
    obtain ⟨q,hq⟩ := (sourceB_parent3_iff r hr).mpr hm
    have hfeed := sourceB_is_original_feeder r hr
    have hq3 : oddTower q 3+2=8*(2*q+3) := by
      simpa using oddTower_factor q 3
    refine ⟨q,(highLevelNext_iff_oddTower
      (oddTower q 3)
      (oddTower (CancellationConstructive.feederQ r)
        (CancellationTerminalConstructive.feederV r))).mpr ?_⟩
    refine ⟨q,3,rfl,?_⟩
    omega

/-- Infinitely many distinct prepared-tape predecessors share each
    cancellation terminal feeder indexed by 9t+7. Both edges are source-level. -/
theorem infinite_two_predecessors (t : Nat) :
    ∃ q3 q4 : Nat,
      highLevelNext (.N (oddTower q3 3)) =
        some (.N (oddTower (CancellationConstructive.feederQ (9*t+7))
          (CancellationTerminalConstructive.feederV (9*t+7)))) ∧
      highLevelNext (.N (oddTower q4 4)) =
        some (.N (oddTower (CancellationConstructive.feederQ (9*t+7))
          (CancellationTerminalConstructive.feederV (9*t+7)))) ∧
      oddTower q3 3 ≠ oddTower q4 4 := by
  obtain ⟨q3,h3⟩ := (cancellation_three_parent_iff (9*t+7) (by omega)).mpr (by omega)
  obtain ⟨q4,h4⟩ := infinite_cancellation_four_parent (3*t+2)
  have he : 3*(3*t+2)+1=9*t+7 := by omega
  rw [he] at h4
  refine ⟨q3,q4,h3,h4,?_⟩
  have hp3 := oddTower_factor q3 3
  have hp4 := oddTower_factor q4 4
  intro hequal
  rw [hequal] at hp3
  have hx : (2:Nat)^3=8 := by decide
  have hy : (2:Nat)^4=16 := by decide
  rw [hx] at hp3
  rw [hy] at hp4
  omega

#print axioms infinite_two_predecessors
#print axioms sourceB_mod19_iff
#print axioms sourceB_parent3_iff
#print axioms cancellation_three_parent_iff
end BB6.Agent46NeedleThree
