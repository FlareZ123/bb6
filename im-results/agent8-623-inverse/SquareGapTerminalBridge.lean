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

/-- One-step quadratic growth bound for the common width envelope. -/
theorem quadratic_step (w : Nat) (hw : 112 <= w) :
    (w+9)*(w+9)+3 <= 3*(w*w+3) := by
  have hww : 112*w <= w*w := by
    calc
      112*w = w*112 := by omega
      _ <= w*w := Nat.mul_le_mul_left w hw
  have hlin : 18*w+84 <= 224*w := by omega
  have h2 : 224*w <= 2*(w*w) := by
    calc
      224*w = 2*(112*w) := by omega
      _ <= 2*(w*w) := Nat.mul_le_mul_left 2 hww
  have hexpand : (w+9)*(w+9)+3 = w*w+18*w+84 := by
    calc
      (w+9)*(w+9)+3 = w*w+9*w+9*w+84 := by
        simp [Nat.add_mul, Nat.mul_add]
        rw [Nat.mul_comm w 9]
        omega
      _ = w*w+18*w+84 := by omega
  rw [hexpand]
  calc
    w*w+18*w+84 <= w*w+224*w := Nat.add_le_add_left hlin (w*w)
    _ <= w*w+2*(w*w) := Nat.add_le_add_left h2 (w*w)
    _ = 3*(w*w) := by omega
    _ <= 3*(w*w)+9 := by omega
    _ = 3*(w*w+3) := by omega

/-- The common width envelope is below the square root of the minimal
ternary scale for every exponent n>=10. -/
theorem width_pow (n : Nat) (hn : 10 <= n) :
    (9*n+22)*(9*n+22)+3 < 3^(n-1) := by
  have hAux : ∀ k : Nat, (9*(k+10)+22)*(9*(k+10)+22)+3 < 3^(k+9) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      let w := 9*(k+10)+22
      have hw : 112 <= w := by dsimp [w]; omega
      have hstep := quadratic_step w hw
      have hI : w*w+3 < 3^(k+9) := by
        have hrew : 9*(k+10)+22 = w := by rfl
        rw [hrew] at ih
        exact ih
      have hmul : 3*(w*w+3) < 3*3^(k+9) :=
        Nat.mul_lt_mul_of_pos_left hI (by decide)
      have hp : 3^(k+10) = 3*3^(k+9) := by
        have heq : k+10 = (k+9)+1 := by omega
        rw [heq, Nat.pow_succ, Nat.mul_comm]
      have hlin : 9*(k+1+10)+22 = w+9 := by
        dsimp [w]
        omega
      rw [hlin, hp]
      exact Nat.lt_of_le_of_lt hstep hmul
  have hlin : 9*n+22 = 9*((n-10)+10)+22 := by omega
  have hexp : n-1 = (n-10)+9 := by omega
  rw [hlin, hexp]
  exact hAux (n-10)

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
    (hwidth : W+9 <= 6*n+41) :
    (W+9)*(W+9) < scale := by
  have hnum := width_pow n hn
  have hpow : (9*n+22)*(9*n+22) < 3^(n-1)-3 := by omega
  have hbound : W+9 <= 9*n+22 := by omega
  have hprod := Nat.mul_le_mul hbound hbound
  omega

theorem left_even_width_small (n W scale : Nat)
    (hn : 10 <= n)
    (hmin : 3^(n-1)-3 <= scale)
    (hwidth : W+5 <= 6*n+28) :
    (W+5)*(W+5) < scale := by
  have hnum := width_pow n hn
  have hpow : (9*n+22)*(9*n+22) < 3^(n-1)-3 := by omega
  have hbound : W+5 <= 9*n+22 := by omega
  have hprod := Nat.mul_le_mul hbound hbound
  omega

theorem right_odd_width_small (n W scale : Nat)
    (hn : 10 <= n)
    (hmin : 3^(n-1)-3 <= scale)
    (hwidth : W+1 <= 6*n+16) :
    (W+1)*(W+1) < scale := by
  have hnum := width_pow n hn
  have hpow : (9*n+22)*(9*n+22) < 3^(n-1)-3 := by omega
  have hbound : W+1 <= 9*n+22 := by omega
  have hprod := Nat.mul_le_mul hbound hbound
  omega

theorem right_even_width_small (n W scale : Nat)
    (hn : 10 <= n)
    (hmin : 3^(n-1)-3 <= scale)
    (hwidth : W+2 <= 9*n+22) :
    (W+2)*(W+2) < scale := by
  have hnum := width_pow n hn
  have hpow : (9*n+22)*(9*n+22) < 3^(n-1)-3 := by omega
  have hprod := Nat.mul_le_mul hwidth hwidth
  omega

/-- Conditional all-sector terminal-window exclusion. The elementary
exponential-versus-quadratic comparison is proved by width_pow. -/
theorem left_odd_terminal_excluded (n W d s : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= d)
    (hwidth : W+9 <= 6*n+41)
    (hlo : -(W : Int) <= (s : Int)-2*(d : Int)+9)
    (hhi : (s : Int)-2*(d : Int)+9 <= W)
    (hsquare : 5*d <= absDiff s (2*d)*absDiff s (2*d)) : False := by
  have hw := left_odd_width_small n W d hn hmin hwidth
  exact left_odd_square_gap_excludes s d W hlo hhi hsquare hw

theorem left_even_terminal_excluded (n W d s : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= d)
    (hwidth : W+5 <= 6*n+28)
    (hlo : -(W : Int) <= (s : Int)-2*(d : Int)+5)
    (hhi : (s : Int)-2*(d : Int)+5 <= W)
    (hsquare : 5*d <= absDiff s (2*d)*absDiff s (2*d)) : False := by
  have hw := left_even_width_small n W d hn hmin hwidth
  exact left_even_square_gap_excludes s d W hlo hhi hsquare hw

theorem right_odd_terminal_excluded (n W a s : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= a)
    (hwidth : W+1 <= 6*n+16)
    (hlo : -(W : Int) <= 2*((s : Int)-(a : Int))+1)
    (hhi : 2*((s : Int)-(a : Int))+1 <= W)
    (hsquare : 5*a <= absDiff s a*absDiff s a) : False := by
  have hw := right_odd_width_small n W a hn hmin hwidth
  exact right_odd_square_gap_excludes s a W hlo hhi hsquare hw

theorem right_even_terminal_excluded (n W a s : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= a)
    (hwidth : W+2 <= 9*n+22)
    (hlo : -(W : Int) <= 2*((s : Int)-(a : Int))+2)
    (hhi : 2*((s : Int)-(a : Int))+2 <= W)
    (hsquare : 5*a <= absDiff s a*absDiff s a) : False := by
  have hw := right_even_width_small n W a hn hmin hwidth
  exact right_even_square_gap_excludes s a W hlo hhi hsquare hw

#print axioms left_odd_terminal_excluded
#print axioms left_even_terminal_excluded
#print axioms right_odd_terminal_excluded
#print axioms right_even_terminal_excluded

end BB6.Agent8SquareGapTerminalBridge
