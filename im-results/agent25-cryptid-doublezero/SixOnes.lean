import TripleIteration
import DoubleZero

namespace CryptidA

theorem a_blank_one_step (m : Nat) :
    run 1 (ab m []) = run 1 (ab m [false]) := by
  simp [run, step, goR, ab]

theorem a_close_nil (m : Nat) :
    run (2*m+6) (ab m []) = finish (2*m+5) [] := by
  calc
    run (2*m+6) (ab m [])
        = run (1+(2*m+5)) (ab m []) := by
            exact congrArg (fun t => run t _) (by omega)
    _ = run (2*m+5) (run 1 (ab m [])) := run_add _ _ _
    _ = run (2*m+5) (run 1 (ab m [false])) := by rw [a_blank_one_step]
    _ = run (1+(2*m+5)) (ab m [false]) := (run_add _ _ _).symm
    _ = run (2*m+6) (ab m [false]) := by
            exact congrArg (fun t => run t _) (by omega)
    _ = finish (2*m+5) [] := close_double_zero m []

theorem a_six_ones (m : Nat) :
    run (14*m+128) (ab m (List.replicate 6 true)) =
      finish (2*m+21) [] := by
  have h : tblock 2 = List.replicate 6 true := by rfl
  calc
    run (14*m+128) (ab m (List.replicate 6 true))
        = run (tcost m 2 + (2*(m+8)+6)) (ab m (tblock 2 ++ [])) := by
            simp only [List.append_nil, h]
            exact congrArg (fun t => run t _) (by simp [tcost]; omega)
    _ = run (2*(m+8)+6) (run (tcost m 2) (ab m (tblock 2 ++ []))) := run_add _ _ _
    _ = run (2*(m+8)+6) (ab (m+4*2) []) := by rw [iter_triplet]
    _ = finish (2*(m+8)+5) [] := by simpa using a_close_nil (m+8)
    _ = finish (2*m+21) [] := by congr 1

#print axioms a_six_ones
end CryptidA
