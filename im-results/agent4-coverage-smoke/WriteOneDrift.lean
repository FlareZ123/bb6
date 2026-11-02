import Frontier
namespace BB6Coverage

def writeOneRight : Move := {write := true, right := true, next := ⟨0,by decide⟩}

def filledRight (n : Nat) : Config :=
  { state := ⟨0, by decide⟩,
    head := (n : Int),
    tape := fun x => decide (0 ≤ x ∧ x < (n : Int)) }

private theorem filledRight_zero : filledRight 0 = blank := by
  simp [filledRight, blank]
  funext x
  simp

private theorem filledRight_read (n : Nat) : readSlot (filledRight n) = initialSlot := by
  simp [readSlot, filledRight, initialSlot]

end BB6Coverage
