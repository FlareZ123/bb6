import P4DeeperFreshRay

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

namespace BB6Coverage

/-- Exact decided/open counts after ten D/0 children under E/0 = 0LC. -/
theorem agent48P4DeeperAudit_report :
    agent48P4DeeperAudit.report =
      (40570882324218750, 19033762451171875) := by
  decide

/-- The extended audit still partitions all 25^12 complete six-state tables. -/
theorem agent48P4DeeperAudit_mass_conservation :
    agent48P4DeeperAudit.report.1 + agent48P4DeeperAudit.report.2 =
      25^12 := by
  rw [agent48P4DeeperAudit_report]
  decide

#print axioms agent48P4DeeperAudit_report
#print axioms agent48P4DeeperAudit_mass_conservation

end BB6Coverage
