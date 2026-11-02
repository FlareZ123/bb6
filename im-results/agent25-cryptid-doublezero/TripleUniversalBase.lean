import DoubleZero

namespace CryptidA

def rightPat : Nat → List Bool
  | 0 => []
  | n + 1 => false :: true :: rightPat n

def ab (m : Nat) (xs : List Bool) : Cfg :=
  ⟨false :: (pat m ++ [true,true]), false, xs, 0⟩

def bphase (m k : Nat) (ys : List Bool) : Cfg :=
  ⟨false :: (pat m ++ [true,true]), false, rightPat k ++ (false :: ys), 1⟩

def lphase (n : Nat) (ys : List Bool) : Cfg :=
  ⟨[], false, [true,true,true,true] ++ rightPat n ++ (false :: ys), 0⟩

def rphase (n : Nat) (ys : List Bool) : Cfg :=
  ⟨[], false, [true,true] ++ rightPat n ++ (false :: ys), 0⟩

def acursor (m n : Nat) (ys : List Bool) : Cfg :=
  ab m (pat n ++ ys)

theorem initial_eight (m : Nat) (ys : List Bool) :
    run 8 (ab m ([true,true,true] ++ ys)) = bphase m 1 ys := by
  simp [run, step, goR, goL, ab, bphase, rightPat]

theorem b_loop (m k : Nat) (ys : List Bool) :
    run 4 (bphase (m+1) k ys) = bphase m (k+1) ys := by
  simp [run, step, goR, goL, bphase, rightPat, pat]

theorem b_walk (m k : Nat) (ys : List Bool) :
    run (4*m) (bphase m k ys) = bphase 0 (m+k) ys := by
  induction m generalizing k with
  | zero => simp [run]
  | succ m ih =>
    calc
      run (4*(m+1)) (bphase (m+1) k ys)
          = run (4*m) (run 4 (bphase (m+1) k ys)) := by
              rw [← run_add]; exact congrArg (fun t => run t _) (by omega)
      _ = run (4*m) (bphase m (k+1) ys) := by rw [b_loop]
      _ = bphase 0 (m+(k+1)) ys := ih (k+1)
      _ = bphase 0 ((m+1)+k) ys := by congr 1; omega

end CryptidA
