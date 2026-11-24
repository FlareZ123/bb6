import BB6Coverage.P4DeeperFreshRay

namespace BB6Coverage

/-- Exact decided/open counts after the P4 eight-child and deeper D/0 grafts. -/
theorem agent48P4DeeperAudit_report :
    agent48P4DeeperAudit.report =
      (40570882080078125, 19033762695312500) := by
  decide

/-- The extended audit still partitions all 25^12 complete six-state tables. -/
theorem agent48P4DeeperAudit_mass_conservation :
    agent48P4DeeperAudit.report.1 + agent48P4DeeperAudit.report.2 =
      25^12 := by
  rw [agent48P4DeeperAudit_report]
  norm_num

#print axioms agent48P4DeeperAudit_report
#print axioms agent48P4DeeperAudit_mass_conservation

end BB6Coverage
