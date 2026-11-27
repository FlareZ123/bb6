import Raw139NormalizedE0CutsFinite
import Raw139NormalizedLocalAcceptedCovers

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedE0Cuts

open BB6Coverage
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedLocalAccepted
open BB6.Agent14Raw139NormalizedE0CutsFinite

/-- Finite reinsertion lemma for the six source-accepted E0 parents. -/
theorem remainingTables_cover_from_61
    (hParents : ∀ q ∈ acceptedE0Six,
      Cover (WeightedBound localScore) q)
    (hNorm : ∀ p ∈ normalizedAfterAcceptedE0Six,
      Cover (WeightedBound localScore) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound localScore) p := by
  intro p hp
  by_cases hHit : matchesAny p acceptedE0Six = true
  · rcases matchesAny_witness hHit with ⟨q, hq, hSame⟩
    rw [BB6.Agent14Raw139Core.sameTable_sound hSame]
    exact hParents q hq
  · exact hNorm p (List.mem_filter.mpr
      ⟨hp, by simp [normalizedAfterAcceptedE0Six, hHit]⟩)

/-- Roster-independent Raw139 local theorem with exactly 61 remaining
    normalized-table Cover hypotheses, conditional only on the six accepted
    E0 parent Covers. -/
theorem raw139_p0_cover_from_61
    (hParents : ∀ q ∈ acceptedE0Six,
      Cover (WeightedBound localScore) q)
    (hNorm : ∀ p ∈ normalizedAfterAcceptedE0Six,
      Cover (WeightedBound localScore) p) :
    Cover (WeightedBound localScore) p0 :=
  raw139_cover_after_accepted_local
    (remainingTables_cover_from_61 hParents hNorm)

/-- Analogous finite reinsertion after ZeroLF: once its parent Cover is
    available, exactly 60 normalized table Covers remain. -/
theorem remainingTables_cover_from_60
    (hParents : ∀ q ∈ acceptedE0Seven,
      Cover (WeightedBound localScore) q)
    (hNorm : ∀ p ∈ normalizedAfterAcceptedE0Seven,
      Cover (WeightedBound localScore) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound localScore) p := by
  intro p hp
  by_cases hHit : matchesAny p acceptedE0Seven = true
  · rcases matchesAny_witness hHit with ⟨q, hq, hSame⟩
    rw [BB6.Agent14Raw139Core.sameTable_sound hSame]
    exact hParents q hq
  · exact hNorm p (List.mem_filter.mpr
      ⟨hp, by simp [normalizedAfterAcceptedE0Seven, hHit]⟩)

theorem raw139_p0_cover_from_60
    (hParents : ∀ q ∈ acceptedE0Seven,
      Cover (WeightedBound localScore) q)
    (hNorm : ∀ p ∈ normalizedAfterAcceptedE0Seven,
      Cover (WeightedBound localScore) p) :
    Cover (WeightedBound localScore) p0 :=
  raw139_cover_after_accepted_local
    (remainingTables_cover_from_60 hParents hNorm)

#print axioms remainingTables_cover_from_61
#print axioms raw139_p0_cover_from_61
#print axioms remainingTables_cover_from_60
#print axioms raw139_p0_cover_from_60

end BB6.Agent14Raw139NormalizedE0Cuts
