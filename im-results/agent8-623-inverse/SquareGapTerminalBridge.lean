import Std

/-!
A standalone arithmetic bridge for the #623 canonical-ray argument.

It converts the four signed terminal-window conditions into bounds on the
absolute old-ray distance, then shows that a square-gap lower bound
5*scale <= distance^2 excludes each window once the corresponding window
width squared is smaller than the scale.

The source-derived root square-gap predicate is deliberately an explicit
hypothesis. This file does not prove that predicate for the blank-root orbit.
-/

namespace BB6.Agent8SquareGapTerminalBridge

def absDiff (x y : Nat) : Nat := if x <= y then y-x else x-y

theorem left_window_absDiff (x y W c : Nat)
    (hlo : -(W : Int) <= (x : Int) - (y : Int) + (c : Int))
    (hhi : (x : Int) - (y : Int) + (c : Int) <= W) :
    absDiff x y <= W+c := by
  unfold absDiff
  by_cases hxy : x <= y
  · simp [hxy]
    omega
  · simp [hxy]
    omega

theorem doubled_window_absDiff (x y W c : Nat)
    (hlo : -(W : Int) <= 2*((x : Int) - (y : Int)) + (c : Int))
    (hhi : 2*((x : Int) - (y : Int)) + (c : Int) <= W) :
    absDiff x y <= W+c := by
  unfold absDiff
  by_cases hxy : x <= y
  · simp [hxy]
    omega
  · simp [hxy]
    omega

theorem square_gap_excludes (dist scale width : Nat)
    (hdist : dist <= width)
    (hsquare : 5*scale <= dist*dist)
    (hwidth : width*width < scale) : False := by
  have hprod : dist*dist <= width*width := Nat.mul_le_mul hdist hdist
  omega

theorem left_odd_square_gap_excludes (s d W : Nat)
    (hlo : -(W : Int) <= (s : Int) - 2*(d : Int) + 9)
    (hhi : (s : Int) - 2*(d : Int) + 9 <= W)
    (hsquare : 5*d <= absDiff s (2*d) * absDiff s (2*d))
    (hwidth : (W+9)*(W+9) < d) : False := by
  have hdist := left_window_absDiff s (2*d) W 9 hlo hhi
  exact square_gap_excludes (absDiff s (2*d)) d (W+9) (by omega) hsquare hwidth

theorem left_even_square_gap_excludes (s d W : Nat)
    (hlo : -(W : Int) <= (s : Int) - 2*(d : Int) + 5)
    (hhi : (s : Int) - 2*(d : Int) + 5 <= W)
    (hsquare : 5*d <= absDiff s (2*d) * absDiff s (2*d))
    (hwidth : (W+5)*(W+5) < d) : False := by
  have hdist := left_window_absDiff s (2*d) W 5 hlo hhi
  exact square_gap_excludes (absDiff s (2*d)) d (W+5) (by omega) hsquare hwidth

theorem right_odd_square_gap_excludes (s a W : Nat)
    (hlo : -(W : Int) <= 2*((s : Int) - (a : Int)) + 1)
    (hhi : 2*((s : Int) - (a : Int)) + 1 <= W)
    (hsquare : 5*a <= absDiff s a * absDiff s a)
    (hwidth : (W+1)*(W+1) < a) : False := by
  have hdist := doubled_window_absDiff s a W 1 hlo hhi
  exact square_gap_excludes (absDiff s a) a (W+1) (by omega) hsquare hwidth

theorem right_even_square_gap_excludes (s a W : Nat)
    (hlo : -(W : Int) <= 2*((s : Int) - (a : Int)) + 2)
    (hhi : 2*((s : Int) - (a : Int)) + 2 <= W)
    (hsquare : 5*a <= absDiff s a * absDiff s a)
    (hwidth : (W+2)*(W+2) < a) : False := by
  have hdist := doubled_window_absDiff s a W 2 hlo hhi
  exact square_gap_excludes (absDiff s a) a (W+2) (by omega) hsquare hwidth

theorem left_odd_width_small (n W scale : Nat)
    (hn : 10 <= n)
    (hmin : 3^(n-1)-3 <= scale)
    (hpow : (9*n+22)*(9*n+22) < 3^(n-1)-3)
    (hwidth : W+9 <= 6*n+41) :
    (W+9)*(W+9) < scale := by
  have hbound : W+9 <= 9*n+22 := by omega
  have hprod := Nat.mul_le_mul hbound hbound
  omega

theorem left_even_width_small (n W scale : Nat)
    (hn : 10 <= n)
    (hmin : 3^(n-1)-3 <= scale)
    (hpow : (9*n+22)*(9*n+22) < 3^(n-1)-3)
    (hwidth : W+5 <= 6*n+28) :
    (W+5)*(W+5) < scale := by
  have hbound : W+5 <= 9*n+22 := by omega
  have hprod := Nat.mul_le_mul hbound hbound
  omega

theorem right_odd_width_small (n W scale : Nat)
    (hn : 10 <= n)
    (hmin : 3^(n-1)-3 <= scale)
    (hpow : (9*n+22)*(9*n+22) < 3^(n-1)-3)
    (hwidth : W+1 <= 6*n+16) :
    (W+1)*(W+1) < scale := by
  have hbound : W+1 <= 9*n+22 := by omega
  have hprod := Nat.mul_le_mul hbound hbound
  omega

theorem right_even_width_small (n W scale : Nat)
    (hn : 10 <= n)
    (hmin : 3^(n-1)-3 <= scale)
    (hpow : (9*n+22)*(9*n+22) < 3^(n-1)-3)
    (hwidth : W+2 <= 9*n+22) :
    (W+2)*(W+2) < scale := by
  have hprod := Nat.mul_le_mul hwidth hwidth
  omega

theorem left_odd_terminal_excluded (n W d s : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= d)
    (hpow : (9*n+22)*(9*n+22) < 3^(n-1)-3)
    (hwidth : W+9 <= 6*n+41)
    (hlo : -(W : Int) <= (s : Int)-2*(d : Int)+9)
    (hhi : (s : Int)-2*(d : Int)+9 <= W)
    (hsquare : 5*d <= absDiff s (2*d)*absDiff s (2*d)) : False := by
  have hw := left_odd_width_small n W d hn hmin hpow hwidth
  exact left_odd_square_gap_excludes s d W hlo hhi hsquare hw

theorem left_even_terminal_excluded (n W d s : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= d)
    (hpow : (9*n+22)*(9*n+22) < 3^(n-1)-3)
    (hwidth : W+5 <= 6*n+28)
    (hlo : -(W : Int) <= (s : Int)-2*(d : Int)+5)
    (hhi : (s : Int)-2*(d : Int)+5 <= W)
    (hsquare : 5*d <= absDiff s (2*d)*absDiff s (2*d)) : False := by
  have hw := left_even_width_small n W d hn hmin hpow hwidth
  exact left_even_square_gap_excludes s d W hlo hhi hsquare hw

theorem right_odd_terminal_excluded (n W a s : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= a)
    (hpow : (9*n+22)*(9*n+22) < 3^(n-1)-3)
    (hwidth : W+1 <= 6*n+16)
    (hlo : -(W : Int) <= 2*((s : Int)-(a : Int))+1)
    (hhi : 2*((s : Int)-(a : Int))+1 <= W)
    (hsquare : 5*a <= absDiff s a*absDiff s a) : False := by
  have hw := right_odd_width_small n W a hn hmin hpow hwidth
  exact right_odd_square_gap_excludes s a W hlo hhi hsquare hw

theorem right_even_terminal_excluded (n W a s : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= a)
    (hpow : (9*n+22)*(9*n+22) < 3^(n-1)-3)
    (hwidth : W+2 <= 9*n+22)
    (hlo : -(W : Int) <= 2*((s : Int)-(a : Int))+2)
    (hhi : 2*((s : Int)-(a : Int))+2 <= W)
    (hsquare : 5*a <= absDiff s a*absDiff s a) : False := by
  have hw := right_even_width_small n W a hn hmin hpow hwidth
  exact right_even_square_gap_excludes s a W hlo hhi hsquare hw

#print axioms left_odd_terminal_excluded
#print axioms left_even_terminal_excluded
#print axioms right_odd_terminal_excluded
#print axioms right_even_terminal_excluded

end BB6.Agent8SquareGapTerminalBridge
