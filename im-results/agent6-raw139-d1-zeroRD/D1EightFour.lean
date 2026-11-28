import D1EightFive
import D8C17Parent
set_option maxHeartbeats 0

namespace BB6.Agent6D1EightFour
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent6D1EightReduce

theorem c17 : Cover (WeightedBound 3000) (sub (move 17)) := by
  have heq : sub (move 17) =
      FAR.fromCodes [7,24,11,24,14,17,8,13,24,24,24,24] := by
    funext ⟨q,b⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide
  rw [heq]
  exact D8C17.cover

theorem cover
    (h2 : Cover (WeightedBound 3000) (sub (move 2)))
    (h16 : Cover (WeightedBound 3000) (sub (move 16)))
    (h18 : Cover (WeightedBound 3000) (sub (move 18)))
    (h19 : Cover (WeightedBound 3000) (sub (move 19))) :
    Cover (WeightedBound 3000) p :=
  BB6.Agent6D1EightFive.cover h2 h16 c17 h18 h19

#print axioms c17
#print axioms cover
end BB6.Agent6D1EightFour
