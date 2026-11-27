import Raw139NormalizedE0TenAcceptedFinite
import Raw139NormalizedE0OneRFConditional

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedE0TenAcceptedConditional

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0TenAcceptedFinite
open BB6.Agent14Raw139NormalizedE0OneRFConditional

/-- The exact ten original normalized E0 parents imply a complete
    normalized Raw139 residual-table Cover from 57 further Covers at
    *any* threshold B. This is a conditional theorem, not a BB(6) bound. -/
theorem remainingTables_cover_from_57 (B : Nat)
    (hParents : ∀ q ∈ acceptedE0Ten, Cover (WeightedBound B) q)
    (hNorm : ∀ p ∈ normalizedAfterTen, Cover (WeightedBound B) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound B) p :=
  remainingTables_cover_from_filter B acceptedE0Ten hParents
    (by simpa [normalizedAfterTen] using hNorm)

/-- Adding the pending exact ZeroLF parent reduces the necessary residual
    hypotheses from 57 to 56, with every halting branch still accounted for. -/
theorem remainingTables_cover_from_56 (B : Nat)
    (hParents : ∀ q ∈ acceptedE0Eleven, Cover (WeightedBound B) q)
    (hNorm : ∀ p ∈ normalizedAfterEleven, Cover (WeightedBound B) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound B) p :=
  remainingTables_cover_from_filter B acceptedE0Eleven hParents
    (by simpa [normalizedAfterEleven] using hNorm)

#print axioms remainingTables_cover_from_57
#print axioms remainingTables_cover_from_56

end BB6.Agent14Raw139NormalizedE0TenAcceptedConditional
