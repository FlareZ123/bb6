import FiveSlotLeafGraft

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace BB6Coverage

/-- Exact numeric report for the depth-four physical frontier after grafting
    the certified five-slot translated nonhalting cylinder. The expected pair
    is the old report plus/minus the exact 25^7 child-cylinder mass. -/
theorem agent27GraftedAudit_report_exact :
    agent27GraftedAudit.report =
      (40570837402343750, 19033807373046875) := by
  decide

#print axioms agent27GraftedAudit_report_exact

end BB6Coverage
