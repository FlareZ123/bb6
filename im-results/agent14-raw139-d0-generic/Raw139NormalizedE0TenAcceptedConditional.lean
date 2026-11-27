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

/-- Exact normalized Raw139 *parent* theorem, not just its 67-row residual
    partition: the original 43 accepted-spine siblings, two continuation
    bridges and terminal champion p7 remain explicit premises. All ten
    already source-certified E0 parent cylinders and the 57 other E0 rows
    appear without duplication, with no global-roster assumption. -/
theorem raw139_p0_cover_from_57 (B : Nat)
    (hb : 59 ≤ B)
    (ha : ∀ r ∈ acceptedRows, Cover (WeightedBound B) (child r.1 r.2))
    (hParents : ∀ q ∈ acceptedE0Ten, Cover (WeightedBound B) q)
    (hNorm : ∀ p ∈ normalizedAfterTen, Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 :=
  BB6.Agent14Raw139Core.raw139_cover B hb ha
    (remainingTables_cover_from_57 B hParents hNorm) hrc hre hf

/-- Eleven-parent specialization when ZeroLF is source-accepted: exactly
    56 normalized raw139 residual table Covers remain, retaining all other
    original source hypotheses and the first-query delay semantics. -/
theorem raw139_p0_cover_from_56 (B : Nat)
    (hb : 59 ≤ B)
    (ha : ∀ r ∈ acceptedRows, Cover (WeightedBound B) (child r.1 r.2))
    (hParents : ∀ q ∈ acceptedE0Eleven, Cover (WeightedBound B) q)
    (hNorm : ∀ p ∈ normalizedAfterEleven, Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 :=
  BB6.Agent14Raw139Core.raw139_cover B hb ha
    (remainingTables_cover_from_56 B hParents hNorm) hrc hre hf

#print axioms remainingTables_cover_from_57
#print axioms remainingTables_cover_from_56
#print axioms raw139_p0_cover_from_57
#print axioms raw139_p0_cover_from_56

end BB6.Agent14Raw139NormalizedE0TenAcceptedConditional
