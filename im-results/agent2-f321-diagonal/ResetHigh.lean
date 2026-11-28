import Phase6
import BulkRuns
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321ResetHigh
open BB6.Agent31F321Density
open BB6.Agent2F321Diagonal
open BB6.Agent2F321Bulk
open BB6.Agent2F321Phase6

/-- A reachable middle-odd branch resets to `(4a+6,1)` with diagonal
    coordinate `x == 4 (mod 8)`. -/
theorem reachable_middleOdd_reset_X_mod8 {n a d : Nat}
    (hr : Reach n a d) (h1 : a < d) (hp : (d-a)%2 = 1) :
    X (4*a+6) 1 % 8 = 4 := by
  have hs := reachable_middleOdd_shape hr h1 hp
  unfold X
  omega

/-- Root-specific infinite-family exclusion. If a reachable middle-odd reset
    is followed only by high branches until a terminal gate, that high-run
    length is 4 mod 8. This strictly sharpens the paper-level generic reset
    condition `k == 0 (mod 4)` by using the all-depth root invariant. -/
theorem middleOdd_high_terminal_length_mod8
    {n k a d A D : Nat}
    (hr : Reach n a d)
    (h1 : a < d) (h2 : d < 3*a+1) (hp : (d-a)%2 = 1)
    (hh : HighRun k (4*a+6) 1 A D)
    (ht : A = D + 1) :
    k % 8 = 4 := by
  have hx : X (4*a+6) 1 % 8 = 4 :=
    reachable_middleOdd_reset_X_mod8 hr h1 hp
  have heq := high_run_terminal_equation hh ht
  have hrhs : (2^k * Y 1) % 8 = 0 := by
    unfold Y
    omega
  omega

/-- The same terminal family in counter-parameter form. -/
theorem middleOdd_high_terminal_parameter
    {n k a d A D : Nat}
    (hr : Reach n a d)
    (h1 : a < d) (h2 : d < 3*a+1) (hp : (d-a)%2 = 1)
    (hh : HighRun k (4*a+6) 1 A D)
    (ht : A = D + 1) :
    k % 8 = 4 ∧ D + 3 = 4 * 2^k := by
  constructor
  · exact middleOdd_high_terminal_length_mod8 hr h1 h2 hp hh ht
  · have hc := high_run_coordinates hh
    have hd := (terminal_iff_diagonal A D).mpr ht
    unfold Y at hc
    omega

/-- Thus the complementary infinite family of generic d=1 reset candidates,
    namely high-run lengths 0 mod 8, is impossible from the authentic root. -/
theorem middleOdd_high_terminal_not_mod8_zero
    {n k a d A D : Nat}
    (hr : Reach n a d)
    (h1 : a < d) (h2 : d < 3*a+1) (hp : (d-a)%2 = 1)
    (hh : HighRun k (4*a+6) 1 A D)
    (ht : A = D + 1) :
    k % 8 ≠ 0 := by
  have hk := middleOdd_high_terminal_length_mod8 hr h1 h2 hp hh ht
  omega

#print axioms reachable_middleOdd_reset_X_mod8
#print axioms middleOdd_high_terminal_length_mod8
#print axioms middleOdd_high_terminal_parameter
#print axioms middleOdd_high_terminal_not_mod8_zero
end BB6.Agent2F321ResetHigh
