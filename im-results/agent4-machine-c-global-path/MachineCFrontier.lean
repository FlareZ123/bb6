import MachineCPath
import LassoTraceAudit

namespace BB6Coverage

set_option maxRecDepth 12000
set_option maxHeartbeats 0

/-- The exact physical successor slots for Machine C's first four
    successful global proof-tree splits. All are source-valid reads,
    rather than an enumeration of hypothetical all-zero control paths. -/
theorem machineC_first_four_global_slots :
    ((List.range 4).map (fun n =>
      firstUnknownPhysical (machineCPrefix n) 12 finiteBlank)) =
      (machineCVisited.take 4).map some := by decide

/-- The source-sound finite-halt, fresh-ray, exact-lasso, and short
    finite-entry macro oracles all decline this particular root path,
    at the exact four-level audit settings used by Agent32. -/
theorem machineC_oracle_false_first_five :
    (List.range 5).map (fun n =>
      lassoDecisionOracle (machineCPrefix n) 6 6 12 2 4) =
        List.replicate 5 false := by decide

/-- True root Machine C is represented by an explicitly unresolved
    leaf in the source-sound global four-level combined audit. The
    theorem says nothing about genuine halting versus nonhalting. -/
theorem machineC_depth_four_open :
    (lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4 4).open
      machineC := by decide

/-- One specific four-row sparse cylinder, containing Machine C, has
    all remaining eight inputs free: 25^8 possible completions. This
    is the cylinder reached by the first four true physical splits. -/
theorem machineC_first_four_mass :
    cylinderMass (machineCPrefix 4) = 25^8 := by decide

#print axioms machineC_first_four_global_slots
#print axioms machineC_oracle_false_first_five
#print axioms machineC_depth_four_open
#print axioms machineC_first_four_mass

end BB6Coverage
