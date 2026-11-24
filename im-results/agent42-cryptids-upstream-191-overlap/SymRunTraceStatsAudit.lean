import SymRunTraceStats

open BusyBeaver.SymRunAudit

/-- Import-closure audit for the two blank-start SymRun token/field range certificates. -/
#check f424_trace_range_certificate
#check f412_trace_range_certificate
#print axioms f424_all_ranges
#print axioms f412_all_ranges
#print axioms f424_checkpoint_chain
#print axioms f412_checkpoint_chain
#print axioms f424_trace_range_certificate
#print axioms f412_trace_range_certificate
