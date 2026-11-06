import LassoTraceAudit

set_option maxRecDepth 12000
set_option maxHeartbeats 0

/- Stronger bounded oracle experiment: lassoLimit=16, entryLimit=4,
   macroLimit=6, physical scanLimit=12, global branch depth=3. -/
#eval (BB6Coverage.lassoPhysicalTraceAudit BB6Coverage.emptyTable 6 6 12 16 4 6 3).report
