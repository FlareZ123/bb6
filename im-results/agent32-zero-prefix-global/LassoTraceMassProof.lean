import LassoTraceAudit

set_option maxRecDepth 12000
set_option maxHeartbeats 0

/-- The depth-three VM report, now checked as a Lean proposition. -/
theorem lassoPhysicalTraceAudit_depth3_report :
    (BB6Coverage.lassoPhysicalTraceAudit BB6Coverage.emptyTable 6 6 12 12 2 4 3).report =
      (33855438232421875, 25749206542968750) := by
  native_decide

/-- The depth-four VM report, now checked as a Lean proposition. -/
theorem lassoPhysicalTraceAudit_depth4_report :
    (BB6Coverage.lassoPhysicalTraceAudit BB6Coverage.emptyTable 6 6 12 12 2 4 4).report =
      (40570831298828125, 19033813476562500) := by
  native_decide

#print axioms lassoPhysicalTraceAudit_depth3_report
#print axioms lassoPhysicalTraceAudit_depth4_report
