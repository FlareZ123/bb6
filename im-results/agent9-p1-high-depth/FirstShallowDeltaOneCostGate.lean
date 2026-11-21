import Lean
open Lean

namespace BB6.Agent9FirstShallowCoordinateGate

/-- Exponential domination used in the B/C defect comparisons. -/
theorem hundred_mul_le_pow_two (n : Nat) (hn : 83 ≤ n) : 100*n ≤ 2^n := by
  induction n, hn using Nat.le_induction with
  | base =>
      decide
  | succ n hn ih =>
      calc
        100*(n+1) ≤ 2*(100*n) := by omega
        _ ≤ 2*2^n := Nat.mul_le_mul_left 2 ih
        _ = 2^(n+1) := by simp [pow_succ, Nat.mul_comm]


/--
For delta=1 and Is=20, a wall immediately after the first shallow edge
would satisfy M+n+2=14u and 22u+4=3P. The unconditional RestartPath
bound M+3<=P makes these equations impossible for n>=83 and 2n<=P.
This deliberately uses hRestart, not the stronger r>=1 terminal cap.
-/
theorem is20_delta1_immediate_terminal_impossible_of_restart_bound
    (P n M u : Nat)
    (hn : 83 ≤ n)
    (hPbig : 2*n ≤ P)
    (hOffset : M+n+2=14*u)
    (hWall : 22*u+4=3*P)
    (hRestart : M+3≤P) : False := by
  omega

/--
For delta=1 and Is=20, the third-position A(0,0) wall equation is
21P=106u+32. Combined with M+n+2=14u and the unconditional RestartPath
bound M+3<=P, it is impossible for n>=83 and 2n<=P.
-/
theorem is20_delta1_A00_third_terminal_impossible_of_restart_bound
    (P n M u : Nat)
    (hn : 83 ≤ n)
    (hPbig : 2*n ≤ P)
    (hOffset : M+n+2=14*u)
    (hWall : 21*P=106*u+32)
    (hRestart : M+3≤P) : False := by
  omega

#print axioms hundred_mul_le_pow_two
#print axioms is20_delta1_immediate_terminal_impossible_of_restart_bound
#print axioms is20_delta1_A00_third_terminal_impossible_of_restart_bound

end BB6.Agent9FirstShallowCoordinateGate
