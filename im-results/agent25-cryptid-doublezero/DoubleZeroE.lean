import DoubleZero

namespace CryptidA

def fstart (r k : Nat) (ys : List Bool) : Cfg :=
  ⟨pat r ++ [true,true], false, List.replicate k true ++ ys, 5⟩

def estart (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false :: false :: (pat m ++ [true,true]), false, false :: ys, 4⟩

theorem e_ten (r : Nat) (ys : List Bool) :
    run 10 (estart (r+1) ys) = fstart r 5 ys := by
  simp [run, step, goL, goR, estart, fstart, pat, List.replicate]

theorem f_three (r k : Nat) (ys : List Bool) :
    run 3 (fstart (r+2) k ys) =
      cursor r 1 (false :: (List.replicate (k+1) true ++ ys)) := by
  simp [run, step, goL, fstart, cursor, pat, List.replicate]

theorem f_long (r k : Nat) (ys : List Bool) :
    run (2*r+7) (fstart (r+2) k ys) =
      finish (2*r+5) (false :: (List.replicate (k+1) true ++ ys)) := by
  calc
    run (2*r+7) (fstart (r+2) k ys)
        = run (2*r+4) (run 3 (fstart (r+2) k ys)) := by
            rw [← run_add]
            congr 1
            omega
    _ = run (2*r+4) (cursor r 1 (false :: (List.replicate (k+1) true ++ ys))) := by
          rw [f_three]
    _ = finish (1+2*r+4) (false :: (List.replicate (k+1) true ++ ys)) :=
          cursor_sweep r 1 _
    _ = finish (2*r+5) (false :: (List.replicate (k+1) true ++ ys)) := by
          congr 1
          omega

theorem e_long (r : Nat) (ys : List Bool) :
    run (2*r+17) (estart (r+3) ys) =
      finish (2*r+5) (false :: (List.replicate 6 true ++ ys)) := by
  calc
    run (2*r+17) (estart (r+3) ys)
        = run (2*r+7) (run 10 (estart (r+3) ys)) := by
            rw [← run_add]
            congr 1
            omega
    _ = run (2*r+7) (fstart (r+2) 5 ys) := by
          simpa using congrArg (run (2*r+7)) (e_ten (r+2) ys)
    _ = finish (2*r+5) (false :: (List.replicate (5+1) true ++ ys)) := f_long r 5 ys
    _ = finish (2*r+5) (false :: (List.replicate 6 true ++ ys)) := by rfl

#print axioms e_long

end CryptidA
