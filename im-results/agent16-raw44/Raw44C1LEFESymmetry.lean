import Raw44CutAssembled
import WeightedSymmetry
import WeightedTNF
import Raw44B1RC_C1R_A1ZeroRF_Symmetry

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw44C1LEFESymmetry
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent16WeightedSymmetry

/-- The sibling five-hole parent with C1 fixed to 0LF. -/
def parentLF : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true  => some (some ⟨false, true, 2⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 2, true  => some (some ⟨false, false, 5⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true  => some (some ⟨true, false, 1⟩)
  | _, _ => none

private abbrev ef : StatePerm := swapStates (4 : Fin 6) 5

theorem renamed_parent :
    renamePartial ef parentLF = BB6.Agent16Raw44Cut.parent := by
  funext s
  rcases s with ⟨q, b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide +kernel

/-- The C1=0LF five-hole child inherits the C1=0LE weighted cover by E/F renaming. -/
theorem c1lf_weighted_bound (m : Machine) (hm : compatible parentLF m) :
    WeightedBound 373 m :=
  weighted_cover_transport 373 ef (by decide +kernel) renamed_parent
    (fun m hm => BB6.Agent16Raw44Cut.weighted_bound m hm) m hm

#print axioms renamed_parent
#print axioms c1lf_weighted_bound
end BB6.Agent16Raw44C1LEFESymmetry
