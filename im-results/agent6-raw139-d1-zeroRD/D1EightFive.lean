import D1EightReduce
import D8C1Parent
import D8C3Parent
import D8C6Parent
set_option maxHeartbeats 0
namespace BB6.Agent6D1EightFive
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent6D1EightReduce

private theorem table_eq (n : Nat) :
    sub (move n) =
      FAR.fromCodes [7,24,11,24,14,n,8,13,24,24,24,24] := by
  funext ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;>
    simp [sub, p, BB6.Agent6D1ZeroRD.sub, move, BB6.Agent6D1ZeroRD.move,
      FAR.fromCodes, FAR.decodeCode, BB6.Agent6D1ZeroRD.p]

theorem c1 : Cover (WeightedBound 3000) (sub (move 1)) := by
  rw [table_eq 1]
  exact D8C1.cover

theorem c3 : Cover (WeightedBound 3000) (sub (move 3)) := by
  rw [table_eq 3]
  exact D8C3.cover

theorem c6 : Cover (WeightedBound 3000) (sub (move 6)) := by
  rw [table_eq 6]
  exact D8C6.cover

theorem cover
    (h2 : Cover (WeightedBound 3000) (sub (move 2)))
    (h16 : Cover (WeightedBound 3000) (sub (move 16)))
    (h17 : Cover (WeightedBound 3000) (sub (move 17)))
    (h18 : Cover (WeightedBound 3000) (sub (move 18)))
    (h19 : Cover (WeightedBound 3000) (sub (move 19))) :
    Cover (WeightedBound 3000) p := by
  apply BB6.Agent6D1EightReduce.cover 3000 (by omega)
  intro n hn
  simp [BB6.Agent6D1EightReduce.hard] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact c1
  · exact h2
  · exact c3
  · exact c6
  · exact h16
  · exact h17
  · exact h18
  · exact h19

#print axioms c1
#print axioms c3
#print axioms c6
#print axioms cover
end BB6.Agent6D1EightFive
