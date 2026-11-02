import TripleUniversalBase

namespace CryptidA

theorem b_tail (k : Nat) (ys : List Bool) :
    run 8 (bphase 0 k ys) = lphase (k+1) ys := by
  simp [run, step, goR, goL, bphase, lphase, rightPat, pat]

theorem middle_ten (n : Nat) (ys : List Bool) :
    run 10 (lphase n ys) = rphase (n+2) ys := by
  simp [run, step, goR, goL, lphase, rphase, rightPat]

theorem rightPat_snoc (n : Nat) : rightPat n ++ [false] = false :: pat n := by
  induction n with
  | zero => simp [rightPat, pat]
  | succ n ih => simp [rightPat, pat, ih]

theorem right_seven (n : Nat) (ys : List Bool) :
    run 7 (rphase n ys) = acursor 0 n ys := by
  cases n with
  | zero => simp [run, step, goR, goL, rphase, acursor, ab, rightPat, pat]
  | succ n =>
    simp [run, step, goR, goL, rphase, acursor, ab, rightPat, pat]
    simpa [List.append_assoc] using congrArg (fun xs : List Bool => xs ++ ys) (rightPat_snoc n)

end CryptidA
