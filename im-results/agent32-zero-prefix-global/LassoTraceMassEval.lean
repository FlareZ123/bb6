import LassoTraceAudit

set_option maxRecDepth 12000
set_option maxHeartbeats 0

/- Interpreted reports for the depth-three and depth-four physical lasso
   frontiers. These are VM counts, not kernel-proved cardinality equalities. -/
#eval (BB6Coverage.lassoPhysicalTraceAudit BB6Coverage.emptyTable 6 6 12 12 2 4 3).report
#eval (BB6Coverage.lassoPhysicalTraceAudit BB6Coverage.emptyTable 6 6 12 12 2 4 4).report
