import CLine
import Quotient1024
namespace Agent41

theorem nextC_eq_CLine (a k c : Nat) :
  nextC a k c = BB6CLine.nextC (a,k,c) := by
  rcases c with _ | _ | _ | _ | c
  · rcases a with _ | _ | a
    · rfl
    · rcases k with _ | k <;> rfl
    · rfl
  · rfl
  · rfl
  · rfl
  · rcases a with _ | a
    · by_cases he : k % 2 = 0
      · have hk : 4*(k/2)+2=2*k+2 := by omega
        simp [nextC, BB6CLine.nextC, he, hk]
      · have hk : 4*(k/2)+5=2*k+3 := by omega
        simp [nextC, BB6CLine.nextC, he, hk]
    · simp [nextC, BB6CLine.nextC]

theorem published_step_is_abstract_edge (a k c : Nat) (t : Nat × Nat × Nat)
    (h : BB6CLine.nextC (a,k,c) = some t) :
    AbstractEdge (q3 (a,k,c)) (q3 t) := by
  apply real_step_is_abstract_edge
  exact (nextC_eq_CLine a k c).trans h

#print axioms nextC_eq_CLine
#print axioms published_step_is_abstract_edge
end Agent41
