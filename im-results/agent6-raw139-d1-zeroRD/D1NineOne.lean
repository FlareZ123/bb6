import D1NineFour
import D9C16Parent
import D9C18Parent
import D9C19Parent
set_option maxHeartbeats 0
namespace BB6.Agent6D1NineOne
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent6D1NineReduce

theorem c16 : Cover (WeightedBound 3000) (sub (move 16)) := by
  have heq : sub (move 16) =
      FAR.fromCodes [7,24,11,24,14,16,9,13,24,24,24,24] := by
    funext ⟨q,b⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide
  rw [heq]
  exact D9C16.cover

theorem c18 : Cover (WeightedBound 3000) (sub (move 18)) := by
  have heq : sub (move 18) =
      FAR.fromCodes [7,24,11,24,14,18,9,13,24,24,24,24] := by
    funext ⟨q,b⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide
  rw [heq]
  exact D9C18.cover

theorem c19 : Cover (WeightedBound 3000) (sub (move 19)) := by
  have heq : sub (move 19) =
      FAR.fromCodes [7,24,11,24,14,19,9,13,24,24,24,24] := by
    funext ⟨q,b⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide
  rw [heq]
  exact D9C19.cover

theorem cover
    (h17 : Cover (WeightedBound 3000) (sub (move 17))) :
    Cover (WeightedBound 3000) p :=
  BB6.Agent6D1NineFour.cover c16 h17 c18 c19

#print axioms c16
#print axioms c18
#print axioms c19
#print axioms cover
end BB6.Agent6D1NineOne
