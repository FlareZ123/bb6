import CancellationParentTwo
import NeedleCancellationFour
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20.CancellationParentTwoSource
open BB6.Agent48.SpaceNeedle
open BB6.Agent47NeedleCancellationFour
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

/-- Exact original published high-level source edge for an infinite,
new valuation-two cancellation feeder progression r=110t+50.
No blank-root reachability is asserted. -/
theorem cancellation_two_parent_source (t:Nat) :
    ∃ p:Nat,
      highLevelNext (.N (oddTower p 2)) =
        some (.N (oddTower
          (CancellationConstructive.feederQ (110*t+50))
          (CancellationTerminalConstructive.feederV (110*t+50)))) := by
  let r:=110*t+50
  obtain ⟨p,hp⟩ := CancellationParentTwo.parent_two_exists t
  change 2^(CancellationGap.valuationA r)*
    CancellationNat.P (2^(CancellationGap.valuationA r)) r + 3 - 4 =
      11*(2*p+3) at hp
  have hpow : 2^(CancellationGap.valuationA r) = 2*2^(NeedleCancelMod35.v r) := by
    rw [valuationA_eq_v_succ r, Nat.pow_succ]
    omega
  have h2B : 2*NeedleCancelMod35.sourceB r =
      2^(CancellationGap.valuationA r)*
        CancellationNat.P (2^(CancellationGap.valuationA r)) r := by
    rw [sourceB_eq_P r, hpow]
    omega
  have hB : NeedleCancelMod35.sourceB r = 11*p+17 := by omega
  have hfeed :
      oddTower (CancellationConstructive.feederQ r)
        (CancellationTerminalConstructive.feederV r)+2 =
      NeedleCancelMod35.sourceB r := by
    exact sourceB_is_original_feeder r (by dsimp [r]; omega)
  have hodd : oddTower p 2+2=4*(2*p+3) := by
    simpa using oddTower_factor p 2
  refine ⟨p,(highLevelNext_iff_oddTower
    (oddTower p 2)
    (oddTower (CancellationConstructive.feederQ r)
      (CancellationTerminalConstructive.feederV r))).mpr ?_⟩
  refine ⟨p,2,rfl,?_⟩
  omega

#print axioms cancellation_two_parent_source
end BB6.Agent20.CancellationParentTwoSource
