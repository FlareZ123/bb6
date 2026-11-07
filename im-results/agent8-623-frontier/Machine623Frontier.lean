import Machine623Path
import LassoTraceAudit

namespace BB6Coverage

set_option maxRecDepth 12000
set_option maxHeartbeats 0

/-- Actual physical first-read route for the four splits of the
    original six-state #623 table, on the blank tape. -/
theorem machine623_first_four_global_slots :
    ((List.range 4).map (fun n =>
      firstUnknownPhysical (machine623Prefix n) 12 finiteBlank)) =
      (machine623Visited.take 4).map some := by decide

/-- The source-certified finite-halt, finite-entry fresh-ray, and
    exact finite lasso oracles do not classify any of these first
    five sparse prefixes at the specified depth-four settings. -/
theorem machine623_oracle_false_first_five :
    (List.range 5).map (fun n =>
      lassoDecisionOracle (machine623Prefix n) 6 6 12 2 4) =
        List.replicate 5 false := by decide

/-- The actual full #623 root lands in an explicitly open leaf of the
    certified-or-open depth-four global audit. This is NOT a nonhalting
    or halting conclusion for #623. -/
theorem machine623_depth_four_open :
    (lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4 4).open
      machine623 := by decide

theorem machine623_first_four_mass :
    cylinderMass (machine623Prefix 4) = 25^8 := by decide

#print axioms machine623_first_four_global_slots
#print axioms machine623_oracle_false_first_five
#print axioms machine623_depth_four_open
#print axioms machine623_first_four_mass

end BB6Coverage
