import P4ZeroRDDeeperGraft

set_option maxRecDepth 8192

namespace BB6Coverage

/-- Exact report after the P4 first-level and both deeper child grafts. -/
theorem agent48P4ZeroRDDeeperAudit_report :
    agent48P4ZeroRDDeeperAudit.report =
      (40570885009765625, 19033759765625000) := by
  decide

/-- Exact mass conservation for the extended P4 audit. -/
theorem agent48P4ZeroRDDeeperAudit_mass_conservation :
    agent48P4ZeroRDDeeperAudit.report.1 +
      agent48P4ZeroRDDeeperAudit.report.2 = 25^12 := by
  rw [agent48P4ZeroRDDeeperAudit_report]
  decide

#print axioms agent48P4ZeroRDDeeperAudit_report
#print axioms agent48P4ZeroRDDeeperAudit_mass_conservation

end BB6Coverage
