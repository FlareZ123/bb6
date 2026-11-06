import AuthenticTurnBranchAudit
import FiniteLassoOracle

namespace BB6.F287

open BB6Coverage

theorem readOneLasso_cover2 :
    Cover (DecidedBelow 2) readOneLassoTable :=
  finiteLassoCheck_sound readOneLassoTable 4 2 readOneLasso_check

noncomputable def authenticLassoAudit :
    FrontierAudit (DecidedBelow 2) emptyTable :=
  addCertificate authenticTurnBranchAudit readOneLassoTable readOneLasso_cover2

theorem authenticLassoAudit_exhaustive (m : Machine) :
    DecidedBelow 2 m ∨ authenticLassoAudit.open m :=
  authenticLassoAudit.exhaustive m (empty_compatible m)

theorem authenticLassoAudit_conserves :
    authenticLassoAudit.report.1 + authenticLassoAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable := authenticLassoAudit.report_conserves
    _ = 25^12 := by decide

#print axioms readOneLasso_cover2
#print axioms authenticLassoAudit_exhaustive
#print axioms authenticLassoAudit_conserves

end BB6.F287
