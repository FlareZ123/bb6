import TripleUniversalBase
namespace CryptidA

theorem ten_pump (m : Nat) (ys : List Bool) :
    run 2 (ab m ([true,false] ++ ys)) = ab (m+1) ys := by
  simp [run, step, goR, ab, pat]

theorem ten_iter (m q : Nat) (ys : List Bool) :
    run (2*q) (ab m (pat q ++ ys)) = ab (m+q) ys := by
  induction q generalizing m with
  | zero => simp [run, pat]
  | succ q ih =>
    calc
      run (2*(q+1)) (ab m (pat (q+1) ++ ys))
          = run (2*q) (run 2 (ab m ([true,false] ++ (pat q ++ ys)))) := by
              rw [← run_add]
              simp only [pat, List.cons_append]
              congr 1; omega
      _ = run (2*q) (ab (m+1) (pat q ++ ys)) := by rw [ten_pump]
      _ = ab ((m+1)+q) ys := ih (m+1)
      _ = ab (m+(q+1)) ys := by congr 1; omega

#print axioms ten_iter
end CryptidA
