import Raw139NormalizedE0OneRFConditional
import Raw139NormalizedE0Cuts

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedE0OneRFCuts

open BB6Coverage
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedLocalAccepted
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedE0OneRFFinite

/-- A source-family Cover over an arbitrary list of eliminated exact physical
    partial tables lifts over the complementary normalized Raw139 frontier.
    This is a finite partition lemma, not a machine halting decision. -/
theorem remaining_cover_from_subset (ps : List PartialMachine)
    (hParents : ∀ q ∈ ps, Cover (WeightedBound localScore) q)
    (hNorm : ∀ p ∈ remainingTables.filter (fun x => !(matchesAny x ps)),
      Cover (WeightedBound localScore) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound localScore) p :=
  BB6.Agent14Raw139NormalizedE0OneRFConditional.remainingTables_cover_from_filter
    localScore ps hParents hNorm

/-- Six existing parents plus accepted OneRF leave sixty actual normalized
    Raw139 subcylinders; only their Covers remain as hypotheses. -/
theorem raw139_p0_cover_from_60_oneRF
    (hParents : ∀ q ∈ acceptedSixPlusOneRF,
      Cover (WeightedBound localScore) q)
    (hNorm : ∀ p ∈ normalizedAfterSixPlusOneRF,
      Cover (WeightedBound localScore) p) :
    Cover (WeightedBound localScore) p0 :=
  raw139_cover_after_accepted_local
    (remaining_cover_from_subset acceptedSixPlusOneRF hParents
      (by simpa [normalizedAfterSixPlusOneRF] using hNorm))

/-- With the additional ZeroLF source Cover, eight accepted parents leave
    fifty-nine normalized subcylinder hypotheses, not a global BB(6) proof. -/
theorem raw139_p0_cover_from_59_eight
    (hParents : ∀ q ∈ acceptedEight,
      Cover (WeightedBound localScore) q)
    (hNorm : ∀ p ∈ normalizedAfterEight,
      Cover (WeightedBound localScore) p) :
    Cover (WeightedBound localScore) p0 :=
  raw139_cover_after_accepted_local
    (remaining_cover_from_subset acceptedEight hParents
      (by simpa [normalizedAfterEight] using hNorm))

#print axioms remaining_cover_from_subset
#print axioms raw139_p0_cover_from_60_oneRF
#print axioms raw139_p0_cover_from_59_eight

end BB6.Agent14Raw139NormalizedE0OneRFCuts
