import Raw139Normalized
import Raw139NormalizedLocalAcceptedCovers

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedE0Cuts

open BB6Coverage
open BB6.Agent6Raw139Normalized
open BB6.Agent31FourHoleRoster
open BB6.Agent14Raw139NormalizedLocalAccepted

/-- Exact normalized Raw139 depth-two E0 rows with source-accepted parent
    certificates as of 2026-11-27. -/
def e0ZeroRA : PartialMachine := leaf (2, ⟨false, true, 0⟩)
def e0ZeroRE : PartialMachine := leaf (2, ⟨false, true, 4⟩)
def e0ZeroRB : PartialMachine := leaf (2, ⟨false, true, 1⟩)
def e0ZeroRD : PartialMachine := leaf (2, ⟨false, true, 3⟩)
def e0ZeroRF : PartialMachine := leaf (2, ⟨false, true, 5⟩)
def e0OneRE  : PartialMachine := leaf (2, ⟨true,  true, 4⟩)

/-- ZeroLF is kept separate until its full parent source audit composes. -/
def e0ZeroLF : PartialMachine := leaf (2, ⟨false, false, 5⟩)

def matchesAny (p : PartialMachine) (ps : List PartialMachine) : Bool :=
  ps.any (fun q => sameTable p q)

def acceptedE0Six : List PartialMachine :=
  [e0ZeroRA, e0ZeroRE, e0ZeroRB, e0ZeroRD, e0ZeroRF, e0OneRE]

def acceptedE0Seven : List PartialMachine :=
  e0ZeroLF :: acceptedE0Six

/-- Each of the six currently accepted E0 parent tables occurs exactly once in
    the 67 normalized Raw139 residual-table frontier. -/
theorem acceptedE0Six_each_once :
    ∀ q ∈ acceptedE0Six,
      (remainingTables.filter (fun p => sameTable p q)).length = 1 := by
  decide

/-- The six accepted E0 tables are pairwise distinct. -/
theorem acceptedE0Six_nodup : acceptedE0Six.Nodup := by
  decide

/-- The normalized local frontier after consuming all six currently accepted
    E0 parents. -/
def normalizedAfterAcceptedE0Six : List PartialMachine :=
  remainingTables.filter (fun p => !(matchesAny p acceptedE0Six))

theorem normalizedAfterAcceptedE0Six_count :
    normalizedAfterAcceptedE0Six.length = 61 := by
  decide

/-- The prospective frontier after also consuming the independently proved
    ZeroLF parent. This is purely a finite table statement and does not claim
    that ZeroLF's parent audit has composed. -/
def normalizedAfterAcceptedE0Seven : List PartialMachine :=
  remainingTables.filter (fun p => !(matchesAny p acceptedE0Seven))

theorem e0ZeroLF_occurs_once :
    (remainingTables.filter (fun p => sameTable p e0ZeroLF)).length = 1 := by
  decide

theorem acceptedE0Seven_nodup : acceptedE0Seven.Nodup := by
  decide

theorem normalizedAfterAcceptedE0Seven_count :
    normalizedAfterAcceptedE0Seven.length = 60 := by
  decide

theorem matchesAny_witness {p : PartialMachine} {ps : List PartialMachine}
    (h : matchesAny p ps = true) :
    ∃ q ∈ ps, sameTable p q = true := by
  simpa [matchesAny] using List.any_eq_true.mp h

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
    rw [sameTable_sound hSame]
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
    rw [sameTable_sound hSame]
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

#print axioms acceptedE0Six_each_once
#print axioms acceptedE0Six_nodup
#print axioms normalizedAfterAcceptedE0Six_count
#print axioms e0ZeroLF_occurs_once
#print axioms acceptedE0Seven_nodup
#print axioms normalizedAfterAcceptedE0Seven_count
#print axioms remainingTables_cover_from_61
#print axioms raw139_p0_cover_from_61
#print axioms remainingTables_cover_from_60
#print axioms raw139_p0_cover_from_60

end BB6.Agent14Raw139NormalizedE0Cuts
