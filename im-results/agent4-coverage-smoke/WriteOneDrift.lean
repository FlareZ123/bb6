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

private theorem filledRight_step (m : Machine) (n : Nat)
    (hm : m initialSlot = some writeOneRight) :
    rawStep m (filledRight n) = some (filledRight (n+1)) := by
  simp only [rawStep, filledRight_read, hm, Option.map_some]
  apply congrArg some
  simp only [applyMove, filledRight, writeOneRight]
  congr 1
  funext x
  by_cases hx : x = (n : Int)
  · subst x
    simp
    omega
  · simp only [hx, ↓reduceIte]
    have hh : (0 ≤ x ∧ x < (n : Int)) ↔ (0 ≤ x ∧ x < ((n+1 : Nat) : Int)) := by
      constructor <;> intro h <;> omega
    simp [hh]

end BB6Coverage
