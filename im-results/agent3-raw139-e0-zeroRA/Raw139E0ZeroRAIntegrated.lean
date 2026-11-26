import Raw139Normalized
import Raw139E0ZeroRAMatch
import A3E0RACover

namespace BB6.Agent3Raw139E0ZeroRAIntegrated

open BB6Coverage BB6Coverage.FAR BB6.Agent6Raw139Normalized BB6.Agent13BlankDelay

/-- The unique six-hole residual cylinder closed by the E0=0RA branch family. -/
def dischargedRow : Fin 7 × Move :=
  BB6.Agent3Raw139E0ZeroRAMatch.row

/-- The remaining normalized residual rows after removing the discharged row. -/
def remainingRowsAfter : List (Fin 7 × Move) :=
  remainingRows.filter (fun r => r != dischargedRow)

/-- The corresponding residual tables; all other Raw139 hypotheses are unchanged. -/
def remainingTablesAfter := remainingRowsAfter.map leaf

theorem dischargedRow_mem : dischargedRow ∈ remainingRows := by
  simpa [dischargedRow] using BB6.Agent3Raw139E0ZeroRAMatch.member

theorem remainingRowsAfter_count : remainingRowsAfter.length = 66 := by
  decide

theorem remainingTablesAfter_count : remainingTablesAfter.length = 66 := by
  decide

theorem discharged_cover :
    Cover (WeightedBound 321796) (leaf dischargedRow) := by
  change Cover (WeightedBound 321796)
    (leaf BB6.Agent3Raw139E0ZeroRAMatch.row)
  rw [BB6.Agent3Raw139E0ZeroRAMatch.exact_table]
  exact BB6.Agent3E0RA.cover

theorem remaining_tables_cover_of_after
    (h : ∀ p ∈ remainingTablesAfter, Cover (WeightedBound 321796) p) :
    ∀ p ∈ remainingTables, Cover (WeightedBound 321796) p := by
  intro p hp
  change p ∈ remainingRows.map leaf at hp
  rcases List.mem_map.mp hp with ⟨r, hr, rfl⟩
  by_cases hrow : r = dischargedRow
  · subst r
    simpa [dischargedRow] using discharged_cover
  · apply h
    apply List.mem_map.mpr
    exact ⟨r, List.mem_filter.mpr ⟨hr, by simp [hrow]⟩, rfl⟩

/-- The Raw139 parent proof now needs only the 66 undisposed residual table Covers. -/
theorem raw139_cover_after
    (ha : ∀ r ∈ acceptedRows,
      Cover (WeightedBound 321796) (child r.1 r.2))
    (hl : ∀ p ∈ remainingTablesAfter, Cover (WeightedBound 321796) p)
    (hrc : Cover (WeightedBound 321796) (leaf rowRC) →
      Cover (WeightedBound 321796) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound 321796) (leaf rowRE) →
      Cover (WeightedBound 321796) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound 321796) p7) :
    Cover (WeightedBound 321796) p0 := by
  exact raw139_cover 321796 (by decide) ha
    (remaining_tables_cover_of_after hl) hrc hre hf

#print axioms discharged_cover
#print axioms remainingRowsAfter_count
#print axioms raw139_cover_after

end BB6.Agent3Raw139E0ZeroRAIntegrated
