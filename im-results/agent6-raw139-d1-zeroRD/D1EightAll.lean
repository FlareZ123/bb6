import D1EightFour
import D8C2Parent
import D8C16Parent
import D8C18Parent
import D8C19Parent
set_option maxHeartbeats 0
namespace BB6.Agent6D1EightAll
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent6D1EightReduce

theorem c2 : Cover (WeightedBound 3000) (sub (move 2)) := by
  have heq : sub (move 2) =
      FAR.fromCodes [7,24,11,24,14,2,8,13,24,24,24,24] := by
    funext ⟨q,b⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide
  rw [heq]
  exact D8C2.cover

theorem c16 : Cover (WeightedBound 3000) (sub (move 16)) := by
  have heq : sub (move 16) =
      FAR.fromCodes [7,24,11,24,14,16,8,13,24,24,24,24] := by
    funext ⟨q,b⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide
  rw [heq]
  exact D8C16.cover

theorem c18 : Cover (WeightedBound 3000) (sub (move 18)) := by
  have heq : sub (move 18) =
      FAR.fromCodes [7,24,11,24,14,18,8,13,24,24,24,24] := by
    funext ⟨q,b⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide
  rw [heq]
  exact D8C18.cover

theorem c19 : Cover (WeightedBound 3000) (sub (move 19)) := by
  have heq : sub (move 19) =
      FAR.fromCodes [7,24,11,24,14,19,8,13,24,24,24,24] := by
    funext ⟨q,b⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide
  rw [heq]
  exact D8C19.cover

/-- The entire D0=8 first-hole cylinder is covered by eight accepted grandchildren. -/
theorem cover : Cover (WeightedBound 3000) p :=
  BB6.Agent6D1EightFour.cover c2 c16 c18 c19

#print axioms c2
#print axioms c16
#print axioms c18
#print axioms c19
#print axioms cover
end BB6.Agent6D1EightAll
