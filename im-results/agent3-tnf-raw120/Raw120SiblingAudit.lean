import FrontierMass
import Raw120RFData
import Raw120RBData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent3Raw120SiblingAudit

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent3Raw120
open BB6.Agent3Raw120RB

/-- Both certified children are lifted to one common local threshold. -/
theorem pRF_weighted_14416 :
    ∀ m, compatible pRF m → WeightedBound 14416 m :=
  allRF

theorem pRB_weighted_14416 :
    ∀ m, compatible pRB m → WeightedBound 14416 m := by
  intro m hm
  have h := allRB m hm
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd) (by decide)

/-- A proof-carrying partial first-hole audit of raw120. The E0=0RF and
    E0=0RB children are certified; the other 23 outcomes (including halt)
    remain explicit unresolved cylinders. -/
def p120Audit : FrontierAudit (WeightedBound 14416) p120 :=
  FrontierAudit.branch p120 (4,false) (by decide) (fun t _ =>
    if hRF : t = some ⟨false,true,5⟩ then
      by
        subst t
        simpa [pRF] using
          (FrontierAudit.certified pRF (Cover.leaf pRF pRF_weighted_14416))
    else if hRB : t = some ⟨false,true,1⟩ then
      by
        subst t
        simpa [pRB] using
          (FrontierAudit.certified pRB (Cover.leaf pRB pRB_weighted_14416))
    else
      FrontierAudit.unresolved (refine p120 (4,false) t))

/-- Every completion of raw120 is either bounded at 14416 or lies in one
    of the 23 explicitly unresolved E0-child cylinders. -/
theorem p120_audit_exhaustive (m : Machine) (hm : compatible p120 m) :
    WeightedBound 14416 m ∨ p120Audit.open m :=
  FrontierAudit.exhaustive p120Audit m hm

/-- Exact full-table mass in the partial audit: two of 25 equal-size
    children are certified, and 23 remain open. -/
theorem p120_audit_report :
    FrontierAudit.report p120Audit = (2 * 25^5, 23 * 25^5) := by
  decide

theorem p120_audit_mass_conservation :
    (FrontierAudit.report p120Audit).1 +
      (FrontierAudit.report p120Audit).2 = 25^6 := by
  calc
    _ = cylinderMass p120 := p120Audit.report_conserves
    _ = 25^6 := by decide

#print axioms pRF_weighted_14416
#print axioms pRB_weighted_14416
#print axioms p120_audit_exhaustive
#print axioms p120_audit_report
#print axioms p120_audit_mass_conservation

end BB6.Agent3Raw120SiblingAudit
