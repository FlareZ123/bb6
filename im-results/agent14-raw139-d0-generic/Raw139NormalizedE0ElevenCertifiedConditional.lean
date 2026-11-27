import Raw139NormalizedE0ElevenCertifiedFinite
import Raw139NormalizedE0TenAcceptedConditional

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedE0ElevenCertifiedConditional

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0ElevenCertifiedFinite
open BB6.Agent14Raw139NormalizedE0TenAcceptedConditional

/-- Exactly eleven already source-certified physical E0 table families:
    their Covers and precisely 56 residual normalized Covers imply the
    *original* Raw139 p0 Cover. No upper-bound or global roster shortcut. -/
theorem remainingTables_cover_from_56_certified (B : Nat)
    (hEleven : ∀ q ∈ acceptedElevenCertified,
      Cover (WeightedBound B) q)
    (h56 : ∀ p ∈ normalizedAfterElevenCertified,
      Cover (WeightedBound B) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound B) p :=
  BB6.Agent14Raw139NormalizedE0OneRFConditional.remainingTables_cover_from_filter
    B acceptedElevenCertified hEleven
    (by simpa [normalizedAfterElevenCertified] using h56)

/-- Prospective E0=0LF proof would leave exactly 55 normalized rows.
    It is an explicit Cover *premise* until source acceptance. -/
theorem remainingTables_cover_from_55_prospective (B : Nat)
    (hTwelve : ∀ q ∈ acceptedTwelveProspective,
      Cover (WeightedBound B) q)
    (h55 : ∀ p ∈ normalizedAfterTwelveProspective,
      Cover (WeightedBound B) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound B) p :=
  BB6.Agent14Raw139NormalizedE0OneRFConditional.remainingTables_cover_from_filter
    B acceptedTwelveProspective hTwelve
    (by simpa [normalizedAfterTwelveProspective] using h55)

/-- Exact original-source Raw139 p0 reduction with all non-E0 obligations
    (43 siblings, 2 continuation bridges, champion p7) still explicit. -/
theorem raw139_p0_cover_from_56_certified (B : Nat)
    (hb : 59 ≤ B)
    (ha : ∀ r ∈ acceptedRows, Cover (WeightedBound B) (child r.1 r.2))
    (hEleven : ∀ q ∈ acceptedElevenCertified,
      Cover (WeightedBound B) q)
    (h56 : ∀ p ∈ normalizedAfterElevenCertified,
      Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 :=
  BB6.Agent14Raw139Core.raw139_cover B hb ha
    (remainingTables_cover_from_56_certified B hEleven h56)
    hrc hre hf

theorem raw139_p0_cover_from_55_prospective (B : Nat)
    (hb : 59 ≤ B)
    (ha : ∀ r ∈ acceptedRows, Cover (WeightedBound B) (child r.1 r.2))
    (hTwelve : ∀ q ∈ acceptedTwelveProspective,
      Cover (WeightedBound B) q)
    (h55 : ∀ p ∈ normalizedAfterTwelveProspective,
      Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 :=
  BB6.Agent14Raw139Core.raw139_cover B hb ha
    (remainingTables_cover_from_55_prospective B hTwelve h55)
    hrc hre hf

#print axioms remainingTables_cover_from_56_certified
#print axioms remainingTables_cover_from_55_prospective
#print axioms raw139_p0_cover_from_56_certified
#print axioms raw139_p0_cover_from_55_prospective

end BB6.Agent14Raw139NormalizedE0ElevenCertifiedConditional
