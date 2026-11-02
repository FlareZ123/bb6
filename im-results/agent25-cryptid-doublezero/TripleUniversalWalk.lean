import TripleUniversalCore
namespace CryptidA
theorem a_loop (m n : Nat) (ys : List Bool) :
    run 2 (acursor m (n+1) ys) = acursor (m+1) n ys := by
  simp [run, step, goR, acursor, ab, pat]
theorem a_walk (m n : Nat) (ys : List Bool) :
    run (2*n) (acursor m n ys) = ab (m+n) ys := by
  induction n generalizing m with
  | zero => simp [run, acursor, ab, pat]
  | succ n ih =>
    calc
      run (2*(n+1)) (acursor m (n+1) ys)
          = run (2*n) (run 2 (acursor m (n+1) ys)) := by
              rw [← run_add]; exact congrArg (fun t => run t _) (by omega)
      _ = run (2*n) (acursor (m+1) n ys) := by rw [a_loop]
      _ = ab ((m+1)+n) ys := ih (m+1)
      _ = ab (m+(n+1)) ys := by congr 1; omega
end CryptidA
