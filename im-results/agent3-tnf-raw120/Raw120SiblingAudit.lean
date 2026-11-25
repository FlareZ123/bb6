import FrontierAudit
import Raw120RFData
import Raw120RBData
import TM63RawUpperInterface

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent3Raw120SiblingAudit

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent3Raw120
open BB6.Agent3Raw120RB
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48DirectRoot
open BB6ChampionArithmetic

/-- The exact published six-state champion score. -/
abbrev championScore : Nat := proposedTM63Moves + 7

theorem championScore_ge_14416 : 14416 ≤ championScore := by
  have hroot : 27959 ≤ threeSectionMoves 27959 3 7 6 63 + 7 := by
    simp only [threeSectionMoves]
    omega
  change 14416 ≤ proposedTM63Moves + 7
  rw [← threeSectionMoves_root]
  omega

/-- Both certified children are lifted to the exact champion score. -/
theorem pRF_weighted_championScore :
    ∀ m, compatible pRF m → WeightedBound championScore m := by
  intro m hm
  have h := allRF m hm
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd) championScore_ge_14416

theorem pRB_weighted_championScore :
    ∀ m, compatible pRB m → WeightedBound championScore m := by
  intro m hm
  have h := allRB m hm
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd)
    (Nat.le_trans (by decide : 223 ≤ 14416) championScore_ge_14416)

/-- A proof-carrying partial first-hole audit of raw120. The E0=0RF and
    E0=0RB children are certified; the other 23 outcomes (including halt)
    remain explicit unresolved cylinders. -/
def p120Audit : FrontierAudit (WeightedBound championScore) p120 :=
  FrontierAudit.branch p120 (4,false) (by decide) (fun t _ =>
    if hRF : t = some ⟨false,true,5⟩ then
      by
        subst t
        simpa [pRF] using
          (FrontierAudit.certified pRF (Cover.leaf pRF pRF_weighted_championScore))
    else if hRB : t = some ⟨false,true,1⟩ then
      by
        subst t
        simpa [pRB] using
          (FrontierAudit.certified pRB (Cover.leaf pRB pRB_weighted_championScore))
    else
      FrontierAudit.unresolved (refine p120 (4,false) t))

/-- Every completion of raw120 is either bounded at the exact champion score or lies in one
    of the 23 explicitly unresolved E0-child cylinders. -/
theorem p120_audit_exhaustive (m : Machine) (hm : compatible p120 m) :
    WeightedBound championScore m ∨ p120Audit.open m :=
  FrontierAudit.exhaustive p120Audit m hm

/-- Exact full-table mass in the partial audit: two of 25 equal-size
    children are certified, and 23 remain open. -/
theorem p120_audit_report :
    FrontierAudit.report p120Audit = (2 * 25^5, 23 * 25^5) := by
  decide

theorem p120_audit_mass_conservation :
    (FrontierAudit.report p120Audit).1 +
      (FrontierAudit.report p120Audit).2 = 25^6 := by
  rw [p120_audit_report]
  norm_num

#print axioms pRF_weighted_championScore
#print axioms pRB_weighted_championScore
#print axioms p120_audit_exhaustive
#print axioms p120_audit_report

end BB6.Agent3Raw120SiblingAudit
