import WordLassoTraceAudit

set_option maxRecDepth 12000
set_option maxHeartbeats 0

/- Exact interpreted reports for the finite-word-augmented physical
   lasso frontier, using the same physical scan and lasso limits as the
   baseline, and entryLimit=3 / macroLimit=4 for the new word oracle. -/
#eval (BB6Coverage.wordLassoPhysicalTraceAudit
  BB6Coverage.emptyTable 6 6 12 12 3 4 3).report

#eval (BB6Coverage.wordLassoPhysicalTraceAudit
  BB6Coverage.emptyTable 6 6 12 12 3 4 4).report
