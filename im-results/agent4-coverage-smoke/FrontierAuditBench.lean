import FrontierAuditSearch
import FrontierClose

namespace BB6Coverage

/-- Existing original-source test cylinder: all A-input slots free, all
other zero-reading slots fixed to halt, all one-reading slots free. -/
def oneHoleAuditedSearch : FrontierAudit (DecidedBelow 2) oneHoleUniversalTable :=
  auditSearch oneHoleUniversalTable 2 0 1

/-- Each of the 25 A/0 branches is certified by the original finite/ray/
zero-mask oracle, leaving no unresolved terminal cylinder in this example. -/
theorem oneHoleAuditedSearch_no_open :
    oneHoleAuditedSearch.report.2 = 0 := by decide

/-- Derives an actual original-source 25-way Cover proof by checking the
reported unexplored mass is exactly zero. -/
theorem oneHoleAuditedSearch_cover :
    Cover (DecidedBelow 2) oneHoleUniversalTable :=
  oneHoleAuditedSearch.complete_of_zero oneHoleAuditedSearch_no_open

theorem oneHoleAuditedSearch_mass :
    oneHoleAuditedSearch.report.1 = 25^7 := by
  have hm := oneHoleAuditedSearch.report_conserves
  rw [oneHoleAuditedSearch_no_open] at hm
  have hc : freeSlotCount oneHoleUniversalTable = 7 := by decide
  simpa [cylinderMass, hc] using hm

#print axioms oneHoleAuditedSearch_no_open
#print axioms oneHoleAuditedSearch_cover
#print axioms oneHoleAuditedSearch_mass
end BB6Coverage
