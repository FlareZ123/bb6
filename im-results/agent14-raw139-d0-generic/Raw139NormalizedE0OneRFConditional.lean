import Raw139NormalizedE0OneRFFinite

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedE0OneRFConditional

open BB6Coverage
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedE0OneRFFinite

/-- A generic exact source-table reinsertion principle at *any* weighted
    primitive-step cutoff, with no assumed global roster or large parent
    proof imports.  It uses literal PartialMachine equality, not heuristic
    table similarity. -/
theorem remainingTables_cover_from_filter (B : Nat) (ps : List PartialMachine)
    (hParents : ∀ q ∈ ps, Cover (WeightedBound B) q)
    (hNorm : ∀ p ∈ remainingTables.filter (fun x => !(matchesAny x ps)),
      Cover (WeightedBound B) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound B) p := by
  intro p hp
  by_cases hHit : matchesAny p ps = true
  · rcases matchesAny_witness hHit with ⟨q, hq, hSame⟩
    rw [BB6.Agent14Raw139Core.sameTable_sound hSame]
    exact hParents q hq
  · exact hNorm p (List.mem_filter.mpr ⟨hp, by simp [hHit]⟩)

/-- Seven exact normalized E0 rows, including source-accepted OneRF, leave
    exactly sixty residual-table Covers at arbitrary bound B. -/
theorem remainingTables_cover_from_60_oneRF (B : Nat)
    (hParents : ∀ q ∈ acceptedSixPlusOneRF, Cover (WeightedBound B) q)
    (hNorm : ∀ p ∈ normalizedAfterSixPlusOneRF,
      Cover (WeightedBound B) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound B) p :=
  remainingTables_cover_from_filter B acceptedSixPlusOneRF hParents
    (by simpa [normalizedAfterSixPlusOneRF] using hNorm)

/-- Eight exact normalized E0 rows, including OneRF and ZeroLF, leave
    exactly fifty-nine residual-table Covers at arbitrary bound B. -/
theorem remainingTables_cover_from_59_eight (B : Nat)
    (hParents : ∀ q ∈ acceptedEight, Cover (WeightedBound B) q)
    (hNorm : ∀ p ∈ normalizedAfterEight,
      Cover (WeightedBound B) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound B) p :=
  remainingTables_cover_from_filter B acceptedEight hParents
    (by simpa [normalizedAfterEight] using hNorm)

#print axioms remainingTables_cover_from_filter
#print axioms remainingTables_cover_from_60_oneRF
#print axioms remainingTables_cover_from_59_eight

end BB6.Agent14Raw139NormalizedE0OneRFConditional
