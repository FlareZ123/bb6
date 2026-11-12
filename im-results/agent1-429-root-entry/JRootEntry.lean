import JPhysicalPrefix
import Lean.Elab.Tactic.Omega

namespace BB429RootEntry

open BB6Coverage BB429PhysicalFrontier BB429JPhysical

/-- Absolute-coordinate configuration of the canonical J(0,0) chart state
    with its head at coordinate 3. -/
def j00Config : Config :=
  { state := ⟨0, by decide⟩
    head := 3
    tape := fun x => jTape 0 0 (x - 3) }

/-- Exact root entry: the original #429 table takes the genuine blank
    A-root to the canonical J(0,0) physical tape in 35 primitive steps. -/
theorem blank_reaches_j00_after_35 :
    run target429 35 blank = some j00Config := by
  simp [run, rawStep, readSlot, target429, prefix11, prefix10, prefix9,
    prefix8, prefix7, prefix6, prefix5, prefix4, prefix3, prefix2,
    prefix1, prefix0]
  ext x <;>
    simp [j00Config, jTape, jMark, jHole] <;>
    omega

#print axioms blank_reaches_j00_after_35

end BB429RootEntry
