import LassoTraceAudit

namespace BB429PhysicalFrontier
open BB6Coverage

/-- Exact eleven ordinary instructions of the unmodified #429 RLE table
    1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA, ordered by the
    first time the genuine blank tape physically consults each input.
    Only the D/1 halt input is left unspecified. -/
def prefix0 : PartialMachine := emptyTable
def prefix1 : PartialMachine :=
  refine prefix0 (⟨0, by decide⟩, false) (some ⟨true, true, ⟨1, by decide⟩⟩)
def prefix2 : PartialMachine :=
  refine prefix1 (⟨1, by decide⟩, false) (some ⟨true, true, ⟨2, by decide⟩⟩)
def prefix3 : PartialMachine :=
  refine prefix2 (⟨2, by decide⟩, false) (some ⟨false, true, ⟨3, by decide⟩⟩)
def prefix4 : PartialMachine :=
  refine prefix3 (⟨3, by decide⟩, false) (some ⟨true, false, ⟨4, by decide⟩⟩)
def prefix5 : PartialMachine :=
  refine prefix4 (⟨4, by decide⟩, false) (some ⟨false, false, ⟨0, by decide⟩⟩)
def prefix6 : PartialMachine :=
  refine prefix5 (⟨0, by decide⟩, true) (some ⟨false, false, ⟨5, by decide⟩⟩)
def prefix7 : PartialMachine :=
  refine prefix6 (⟨5, by decide⟩, true) (some ⟨true, false, ⟨0, by decide⟩⟩)
def prefix8 : PartialMachine :=
  refine prefix7 (⟨1, by decide⟩, true) (some ⟨true, true, ⟨0, by decide⟩⟩)
def prefix9 : PartialMachine :=
  refine prefix8 (⟨2, by decide⟩, true) (some ⟨false, true, ⟨1, by decide⟩⟩)
def prefix10 : PartialMachine :=
  refine prefix9 (⟨5, by decide⟩, false) (some ⟨true, true, ⟨3, by decide⟩⟩)
def prefix11 : PartialMachine :=
  refine prefix10 (⟨4, by decide⟩, true) (some ⟨true, false, ⟨4, by decide⟩⟩)

/-- The next genuinely consulted input in each sparse physical prefix.
    In particular the scanner reaches a read-one row before the sixth
    read-zero row; the exact first-visit times are recorded below. -/
theorem firstUnknown0 :
    firstUnknownPhysical prefix0 25 finiteBlank = some (⟨0, by decide⟩, false) := by decide
theorem firstUnknown1 :
    firstUnknownPhysical prefix1 25 finiteBlank = some (⟨1, by decide⟩, false) := by decide
theorem firstUnknown2 :
    firstUnknownPhysical prefix2 25 finiteBlank = some (⟨2, by decide⟩, false) := by decide
theorem firstUnknown3 :
    firstUnknownPhysical prefix3 25 finiteBlank = some (⟨3, by decide⟩, false) := by decide
theorem firstUnknown4 :
    firstUnknownPhysical prefix4 25 finiteBlank = some (⟨4, by decide⟩, false) := by decide
theorem firstUnknown5 :
    firstUnknownPhysical prefix5 25 finiteBlank = some (⟨0, by decide⟩, true) := by decide
theorem firstUnknown6 :
    firstUnknownPhysical prefix6 25 finiteBlank = some (⟨5, by decide⟩, true) := by decide
theorem firstUnknown7 :
    firstUnknownPhysical prefix7 25 finiteBlank = some (⟨1, by decide⟩, true) := by decide
theorem firstUnknown8 :
    firstUnknownPhysical prefix8 25 finiteBlank = some (⟨2, by decide⟩, true) := by decide
theorem firstUnknown9 :
    firstUnknownPhysical prefix9 25 finiteBlank = some (⟨5, by decide⟩, false) := by decide
theorem firstUnknown10 :
    firstUnknownPhysical prefix10 25 finiteBlank = some (⟨4, by decide⟩, true) := by decide

/-- The machine's first 25 raw queries never consult the last unassigned
    D/1 halting row. This bounded statement does not imply nonhalting. -/
theorem no_hole_within_25 :
    firstUnknownPhysical prefix11 25 finiteBlank = none := by decide

/-- All eleven ordinary rules are fixed. The only unassigned input row
    is the authentic D/1 halting instruction, and this fact uses all
    twelve actual state-symbol slots. -/
theorem unique_remaining_slot :
    ∀ slot : Slot, prefix11 slot = none ↔
      slot = (⟨3, by decide⟩, true) := by decide

/-- Canonical exact total #429 transition table: the eleven ordinary
    actions above and the unique final D/1 halt. -/
def target429 : Machine := fun s =>
  match prefix11 s with
  | some action => action
  | none => none

theorem target429_compatible : compatible prefix11 target429 := by
  intro s t h
  simp only [target429]
  simp only [h]
theorem target429_halt_slot : target429 (⟨3, by decide⟩, true) = none := by decide

/-- A source-sound authentic raw trace forces a physically valid A/1
    branch after the first five rules for every full compatible table.
    This is an actual read-one cell, not a hypothetical zero-row path. -/
theorem prefix5_genuine_read_one_branch (m : Machine)
    (hm : compatible prefix5 m) :
    ∃ k, k < 25 ∧ ∃ d : FinRayCfg,
      run m k (embedFinRay finiteBlank) = some (embedFinRay d) ∧
      (⟨0, by decide⟩, true) = (d.state, finiteTape d d.head) ∧
      prefix5 (⟨0, by decide⟩, true) = none :=
  firstUnknownPhysical_is_raw_prefix prefix5 m hm 25 finiteBlank _
    firstUnknown5

/-- Existing short universal decision, finite-lasso and fresh-ray
    predicates fail on this root-compatible eleven-row partial table.
    A false oracle result is an explicitly open proof leaf. -/
theorem prefix11_oracle_open :
    lassoDecisionOracle prefix11 6 6 12 2 4 = false := by decide

#print axioms firstUnknown5
#print axioms firstUnknown10
#print axioms no_hole_within_25
#print axioms unique_remaining_slot
#print axioms target429_compatible
#print axioms prefix5_genuine_read_one_branch
#print axioms prefix11_oracle_open
end BB429PhysicalFrontier
