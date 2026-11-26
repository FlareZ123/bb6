import Canonical64Raw139Subcover
import Raw139E0ZeroRAIntegrated

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Canonical64Raw139Crosswalk

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleRoster
open BB6.Agent6Raw139Normalized
open BB6.Agent3Raw139E0ZeroRAIntegrated
open BB6.Agent14Canonical64Raw139Subcover

/-- p is a partial table whose fixed transitions are all retained identically
    in q. Thus every completion of q is also a completion of p. -/
def Extends (p q : PartialMachine) : Prop :=
  ∀ slot, p slot = none ∨ q slot = p slot

/-- Boolean form used by the finite crosswalk. -/
def extendsTable (p q : PartialMachine) : Bool := decide (Extends p q)

theorem extendsTable_sound {p q : PartialMachine}
    (h : extendsTable p q = true) : Extends p q :=
  of_decide_eq_true h

theorem compatible_of_extends {p q : PartialMachine} {m}
    (he : Extends p q) (hm : compatible q m) : compatible p m := by
  intro slot v hp
  have hq : q slot = some v := by
    rcases he slot with hnone | heq
    · rw [hp] at hnone
      contradiction
    · rw [heq, hp]
  exact hm slot v hq

/-- A Cover is inherited by every more-specific partial table. -/
theorem cover_of_extends {B : Nat} {p q : PartialMachine}
    (h : Cover (WeightedBound B) p) (he : Extends p q) :
    Cover (WeightedBound B) q := by
  cases h with
  | leaf _ hbound =>
      exact Cover.leaf _ (fun m hm k d hk hd =>
        hbound m (compatible_of_extends he hm) k d hk hd)

/-- The active Canonical64 Raw139 leaves after the accepted 0RA Cover. -/
def activeRows := remainingRaw139AfterFortyThreeWithoutE0

/-- The 66 unresolved normalized Raw139 tables after the accepted 0RA Cover. -/
def normalizedTables := remainingTablesAfter

def activeCoveredByNormalized : List (List Move × PartialMachine) :=
  activeRows.filter (fun e =>
    normalizedTables.any (fun p => extendsTable p e.2))

def activeUncoveredByNormalized : List (List Move × PartialMachine) :=
  activeRows.filter (fun e =>
    !(normalizedTables.any (fun p => extendsTable p e.2))

/-- Number of active leaves subsumed by each normalized residual table. -/
def activeCoverageCounts : List Nat :=
  normalizedTables.map (fun p =>
    (activeRows.filter (fun e => extendsTable p e.2)).length)

def normalizedCoverageSummary : List (Fin 7 × Move × Nat) :=
  (remainingRowsAfter.zip activeCoverageCounts).map
    (fun x => (x.1.1, x.1.2, x.2))

def normalizedCoveredByActive : List PartialMachine :=
  normalizedTables.filter (fun p =>
    activeRows.any (fun e => extendsTable e.2 p))

def e0LCTable : PartialMachine := leaf (2, ⟨false, false, 2⟩)

/-- A finite crosswalk can discharge every active row covered by at least one
    normalized residual Cover. -/
theorem activeCoveredByNormalized_cover (B : Nat)
    (hNorm : ∀ p ∈ normalizedTables, Cover (WeightedBound B) p) :
    ∀ e ∈ activeCoveredByNormalized, Cover (WeightedBound B) e.2 := by
  intro e he
  have hAny : normalizedTables.any (fun p => extendsTable p e.2) = true :=
    (List.mem_filter.mp he).2
  obtain ⟨p, hp, hExt⟩ := List.any_eq_true.mp hAny
  exact cover_of_extends (hNorm p hp) (extendsTable_sound hExt)

/-- If the finite crosswalk misses some active rows, only those explicit
    complement rows need separate Covers in addition to the normalized list. -/
theorem activeRows_cover_from_normalized_and_complement (B : Nat)
    (hNorm : ∀ p ∈ normalizedTables, Cover (WeightedBound B) p)
    (hRest : ∀ e ∈ activeUncoveredByNormalized, Cover (WeightedBound B) e.2) :
    ∀ e ∈ activeRows, Cover (WeightedBound B) e.2 := by
  intro e he
  by_cases hCovered : normalizedTables.any (fun p => extendsTable p e.2) = true
  · obtain ⟨p, hp, hExt⟩ := List.any_eq_true.mp hCovered
    exact cover_of_extends (hNorm p hp) (extendsTable_sound hExt)
  · have hAnyFalse : normalizedTables.any (fun p => extendsTable p e.2) = false := by
      cases hAny : normalizedTables.any (fun p => extendsTable p e.2) with
      | false => rfl
      | true => exact (hCovered hAny).elim
    have hUncovered : e ∈ activeUncoveredByNormalized := by
      apply List.mem_filter.mpr
      exact ⟨he, by simp [activeUncoveredByNormalized, hAnyFalse]⟩
    exact hRest e hUncovered

/-- Strongest possible case: every active 79-leaf is a refinement of one of
    the 66 normalized residual tables. -/
theorem activeRows_cover_from_normalized (B : Nat)
    (hCross : ∀ e ∈ activeRows, ∃ p ∈ normalizedTables, Extends p e.2)
    (hNorm : ∀ p ∈ normalizedTables, Cover (WeightedBound B) p) :
    ∀ e ∈ activeRows, Cover (WeightedBound B) e.2 := by
  intro e he
  obtain ⟨p, hp, hExt⟩ := hCross e he
  exact cover_of_extends (hNorm p hp) hExt

/-- Canonical64 exactness interface using the 66 normalized residual Covers
    plus Covers only for active leaves outside the finite refinement crosswalk. -/
theorem exact_at_target_with_normalized_and_complement
    (hOther : ∀ e ∈ roster64,
      e.2 ≠ championResidual →
        Cover (WeightedBound (proposedTM63Moves + 7)) e.2)
    (hNorm : ∀ p ∈ normalizedTables,
      Cover (WeightedBound (proposedTM63Moves + 7)) p)
    (hRest : ∀ e ∈ activeUncoveredByNormalized,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent14Canonical64Raw139Subcover.exact_at_target_with_raw139_subcover
    hOther
    (activeRows_cover_from_normalized_and_complement
      (proposedTM63Moves + 7) hNorm hRest)

/-- If the refinement crosswalk is total, the global conditional interface
    needs only 63 other Canonical64 Covers and 66 normalized Raw139 Covers. -/
theorem exact_at_target_with_normalized_if_crosswalk
    (hCross : ∀ e ∈ activeRows, ∃ p ∈ normalizedTables, Extends p e.2)
    (hOther : ∀ e ∈ roster64,
      e.2 ≠ championResidual →
        Cover (WeightedBound (proposedTM63Moves + 7)) e.2)
    (hNorm : ∀ p ∈ normalizedTables,
      Cover (WeightedBound (proposedTM63Moves + 7)) p) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent14Canonical64Raw139Subcover.exact_at_target_with_raw139_subcover
    hOther
    (activeRows_cover_from_normalized
      (proposedTM63Moves + 7) hCross hNorm)

/-- Finite crosswalk diagnostics. The first count is how many active leaves
    are refinements of at least one normalized residual table; the second is
    how many are not. The final counts test E0=0LC by exact equality and by
    the more useful refinement relation. -/
#eval (normalizedTables.length, activeRows.length,
  activeCoveredByNormalized.length, activeUncoveredByNormalized.length)
#eval normalizedCoverageSummary
#eval activeUncoveredByNormalized.map (fun e => e.1)
#eval normalizedCoveredByActive.length
#eval (activeRows.filter (fun e => sameTable e.2 e0LCTable)).length
#eval (activeRows.filter (fun e => extendsTable e0LCTable e.2)).map (fun e => e.1)

#print axioms compatible_of_extends
#print axioms cover_of_extends
#print axioms activeRows_cover_from_normalized_and_complement
#print axioms activeRows_cover_from_normalized
#print axioms exact_at_target_with_normalized_and_complement
#print axioms exact_at_target_with_normalized_if_crosswalk

end BB6.Agent14Canonical64Raw139Crosswalk
