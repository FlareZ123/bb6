import Raw139NormalizedLocalAcceptedCovers
import Raw139NormalizedE0ParentRows
import Raw139E0ZeroRAIntegrated
import Raw139E0ZeroRECover
import Raw139E0ZeroRBCover
import Raw139E0ZeroRDCover
import E0ZeroLFDischarge

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedZeroLF62Local

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent6Raw139Normalized
open BB6.Agent31FourHoleRoster
open BB6.Agent3Raw139E0ZeroRAIntegrated
open BB6.Agent14Raw139NormalizedE0ParentRows
open BB6.Agent14Raw139NormalizedLocalAccepted
open BB6.Agent38ChampionThreshold

/-- Monotonicity for an already constructed partial-machine Cover. -/
theorem cover_mono {A B : Nat} (hAB : A ≤ B) {p : PartialMachine}
    (h : Cover (WeightedBound A) p) : Cover (WeightedBound B) p := by
  cases h with
  | leaf _ hbound =>
      refine Cover.leaf _ ?_
      intro m hm k d hk hd
      exact Nat.le_trans (hbound m hm k d hk hd) hAB

/-- Lift the already accepted E0=0RA six-hole parent to the fixed local score. -/
theorem e0RA_cover_at_localScore :
    Cover (WeightedBound localScore) (leaf dischargedRow) := by
  exact cover_mono
    (by have h := localScore_ge_6766859; omega)
    discharged_cover

theorem e0RETable_eq_certifiedParent :
    e0RETable = BB6.Agent48Raw139E0ZeroRE.parent := by
  exact sameTable_sound (by decide)

theorem e0RBTable_eq_certifiedParent :
    e0RBTable = BB6.Agent48Raw139E0ZeroRB.parent := by
  exact sameTable_sound (by decide)

theorem e0RDTable_eq_certifiedParent :
    e0RDTable = BB6.Agent48Raw139E0ZeroRD.parent := by
  exact sameTable_sound (by decide)

theorem e0RE_cover_at_localScore :
    Cover (WeightedBound localScore) e0RETable := by
  rw [e0RETable_eq_certifiedParent]
  exact liftWeighted (by decide : 852 ≤ 6766859)
    BB6.Agent48Raw139E0ZeroRE.all_completions_weighted

theorem e0RB_cover_at_localScore :
    Cover (WeightedBound localScore) e0RBTable := by
  rw [e0RBTable_eq_certifiedParent]
  exact liftWeighted (by decide : 1217 ≤ 6766859)
    BB6.Agent48Raw139E0ZeroRB.all_completions_weighted

theorem e0RD_cover_at_localScore :
    Cover (WeightedBound localScore) e0RDTable := by
  rw [e0RDTable_eq_certifiedParent]
  exact liftWeighted (by decide : 806 ≤ 6766859)
    BB6.Agent48Raw139E0ZeroRD.all_completions_weighted

/-- Reinsert the three accepted E0 parent rows into the 66-row post-0RA list. -/
theorem normalizedTables_cover_from_63
    (hNorm : ∀ p ∈ normalizedTablesWithoutE0RE0RB0RD,
      Cover (WeightedBound localScore) p) :
    ∀ p ∈ normalizedTables, Cover (WeightedBound localScore) p := by
  intro p hp
  by_cases hRE : sameTable p e0RETable = true
  · rw [sameTable_sound hRE]
    exact e0RE_cover_at_localScore
  · by_cases hRB : sameTable p e0RBTable = true
    · rw [sameTable_sound hRB]
      exact e0RB_cover_at_localScore
    · by_cases hRD : sameTable p e0RDTable = true
      · rw [sameTable_sound hRD]
        exact e0RD_cover_at_localScore
      · exact hNorm p (List.mem_filter.mpr
          ⟨hp, by simp [normalizedTablesWithoutE0RE0RB0RD, hRE, hRB, hRD]⟩)

/-- Reinsert E0=0RA as well, recovering all 67 normalized Raw139 residual
    tables without referring to any canonical quotient roster. -/
theorem remainingTables_cover_from_63
    (hNorm : ∀ p ∈ normalizedTablesWithoutE0RE0RB0RD,
      Cover (WeightedBound localScore) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound localScore) p := by
  intro p hp
  change p ∈ remainingRows.map leaf at hp
  rcases List.mem_map.mp hp with ⟨r, hr, rfl⟩
  by_cases hRA : r = dischargedRow
  · subst r
    exact e0RA_cover_at_localScore
  · have hpAfter : leaf r ∈ normalizedTables := by
      apply List.mem_map.mpr
      exact ⟨r, List.mem_filter.mpr ⟨hr, by simp [dischargedRow, hRA]⟩, rfl⟩
    exact normalizedTables_cover_from_63 hNorm (leaf r) hpAfter

/-- The normalized E0=0LF row closed by Agent14's source-audited parent. -/
def e0LFTable : PartialMachine := leaf (2, ⟨false, false, 5⟩)

theorem e0LF_occurs_once :
    (normalizedTablesWithoutE0RE0RB0RD.filter
      (fun p => sameTable p e0LFTable)).length = 1 := by
  decide

/-- The local normalized Raw139 frontier after all five accepted E0 parents. -/
def normalizedTablesWithoutE0Parents : List PartialMachine :=
  normalizedTablesWithoutE0RE0RB0RD.filter
    (fun p => !(sameTable p e0LFTable))

theorem normalizedTablesWithoutE0Parents_count :
    normalizedTablesWithoutE0Parents.length = 62 := by
  decide

theorem e0LFTable_eq_certifiedParent :
    e0LFTable = BB6.Agent14E0LFParent.parent := by
  exact sameTable_sound (by decide)

theorem e0LF_cover_at_localScore :
    Cover (WeightedBound localScore) e0LFTable := by
  rw [e0LFTable_eq_certifiedParent]
  exact cover_mono
    (by have h := localScore_ge_6766859; omega)
    BB6.Agent14E0LFParent.weighted

/-- Reinsert ZeroLF, recovering the 63-row post-E0RA/RE/RB/RD frontier. -/
theorem normalized63_cover_from_62
    (hNorm : ∀ p ∈ normalizedTablesWithoutE0Parents,
      Cover (WeightedBound localScore) p) :
    ∀ p ∈ normalizedTablesWithoutE0RE0RB0RD,
      Cover (WeightedBound localScore) p := by
  intro p hp
  by_cases hLF : sameTable p e0LFTable = true
  · rw [sameTable_sound hLF]
    exact e0LF_cover_at_localScore
  · exact hNorm p (List.mem_filter.mpr
      ⟨hp, by simp [normalizedTablesWithoutE0Parents, hLF]⟩)

/-- Covers for exactly 62 remaining normalized rows recover all 67 local
    Raw139 unresolved-table Covers. -/
theorem remainingTables_cover_from_62
    (hNorm : ∀ p ∈ normalizedTablesWithoutE0Parents,
      Cover (WeightedBound localScore) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound localScore) p :=
  remainingTables_cover_from_63 (normalized63_cover_from_62 hNorm)

/-- Roster-independent 62-row Raw139 theorem. This is the local result that
    global quotient consumers should import. -/
theorem raw139_p0_cover_from_62
    (hNorm : ∀ p ∈ normalizedTablesWithoutE0Parents,
      Cover (WeightedBound localScore) p) :
    Cover (WeightedBound localScore) p0 :=
  raw139_cover_after_accepted_local (remainingTables_cover_from_62 hNorm)

#print axioms e0RA_cover_at_localScore
#print axioms e0RETable_eq_certifiedParent
#print axioms e0RBTable_eq_certifiedParent
#print axioms e0RDTable_eq_certifiedParent
#print axioms e0RE_cover_at_localScore
#print axioms e0RB_cover_at_localScore
#print axioms e0RD_cover_at_localScore
#print axioms normalizedTables_cover_from_63
#print axioms remainingTables_cover_from_63
#print axioms e0LF_occurs_once
#print axioms normalizedTablesWithoutE0Parents_count
#print axioms e0LFTable_eq_certifiedParent
#print axioms e0LF_cover_at_localScore
#print axioms normalized63_cover_from_62
#print axioms remainingTables_cover_from_62
#print axioms raw139_p0_cover_from_62

end BB6.Agent14Raw139NormalizedZeroLF62Local
