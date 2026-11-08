import TranslatedFiniteOracle
import LassoTraceAudit

namespace BB6Coverage

/-- The moving two-marker machine enters a translated exact cycle. -/
theorem movingPair_new_certificate :
    finiteTranslatedCheck movingPairTable 2 5 = true := movingPair_check

/-- The previous combined finite-halt, pristine-ray, exact-lasso, finite-entry
    fresh-ray and zero-mask oracle has no certificate for this partial table,
    even with discovery limits enlarged to twelve transitions each. -/
theorem movingPair_old_combined_misses :
    lassoDecisionOracle movingPairTable 6 12 12 12 12 = false := by decide

/-- This genuinely new source-sound proof family has seven assigned transition
    slots and five free slots in a complete six-state two-symbol table. -/
theorem movingPair_cylinder_mass :
    cylinderMass movingPairTable = 25^5 := by decide

#print axioms movingPair_old_combined_misses
#print axioms movingPair_cylinder_mass
end BB6Coverage
