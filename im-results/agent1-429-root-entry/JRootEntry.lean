import BB429PhysicalFrontier
import Lean.Elab.Tactic.Omega

namespace BB429RootEntry

open BB6Coverage BB429PhysicalFrontier

/-- The physical J(0,0) tape, relative to its A-head: six consecutive
    ones on [-6,1], a blank at 2, and a final one at 3.  This is exactly
    jTape 0 0 from BB429JPhysical.jMark/jHole. -/
def j00Tape (x : Int) : Bool :=
  decide ((-6 : Int) ≤ x ∧ x ≤ 1 ∨ x = 3)

/-- Absolute-coordinate configuration reached from the genuine blank
    A-root after 35 ordinary transitions. -/
def j00Config : Config :=
  { state := ⟨0, by decide⟩
    head := 3
    tape := fun x => j00Tape (x - 3) }

/-- Exact root entry: the original #429 table takes the blank A-root to
    the canonical J(0,0) tape in 35 primitive steps. -/
theorem blank_reaches_j00_after_35 :
    run target429 35 blank = some j00Config := by
  apply Option.some.inj
  ext x <;>
    simp [j00Config, j00Tape, run, rawStep, applyMove, readSlot,
      target429, prefix11, prefix10, prefix9, prefix8, prefix7, prefix6,
      prefix5, prefix4, prefix3, prefix2, prefix1, prefix0, emptyTable] <;>
    omega

#print axioms blank_reaches_j00_after_35

end BB429RootEntry
