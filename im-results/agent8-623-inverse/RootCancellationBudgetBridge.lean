import Std
import SquareGapTerminalBridge

namespace BB6.Agent8RootCancellationBudgetBridge
open BB6.Agent8SquareGapTerminalBridge

def absDiff (x y : Nat) : Nat := if x <= y then y-x else x-y

theorem absDiff_le_both (x y E : Nat) (h : absDiff x y <= E) :
    x <= y+E /\ y <= x+E := by
  unfold absDiff at h
  by_cases hxy : x <= y
  · simp [hxy] at h
    omega
  · simp [hxy] at h
    omega

theorem min_scale_large (n m : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= m) :
    100*n+500 <= m := by
  have hnum := width_pow n hn
  have hw : 112 <= 9*n+22 := by omega
  have hmul := Nat.mul_le_mul_left (9*n+22) hw
  have hlin : 100*n+503 <= 112*(9*n+22) := by omega
  have hbase : 100*n+503 <= (9*n+22)*(9*n+22) := by
    calc
      100*n+503 <= 112*(9*n+22) := hlin
      _ = (9*n+22)*112 := by omega
      _ <= (9*n+22)*(9*n+22) := hmul
  omega

theorem pow_six (n : Nat) : 3^(n+6) = 729*3^n := by
  calc
    3^(n+6) = 3^n*3^6 := by rw [Nat.pow_add]
    _ = 3^n*729 := by rw [show 3^6=729 by decide]
    _ = 729*3^n := by exact Nat.mul_comm _ _

theorem outer_left_budget (n m u E : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= m)
    (hmax : m+3 < 3^n) (hE : E <= 35*n+120)
    (hgap : absDiff u (13*m) <= E) :
    9*m+39+(n+6) <= u /\ 14*m+59 <= 3^(n+6) := by
  have hlarge := min_scale_large n m hn hmin
  have hg := absDiff_le_both u (13*m) E hgap
  have hroom : E+39+(n+6) <= 4*m := by omega
  have hfirst : 9*m+39+(n+6) <= u := by omega
  have hm : m < 3^n := by omega
  have hp := pow_six n
  have hpos : 1 <= 3^n := by exact Nat.one_le_pow n 3 (by decide)
  have hpower : 14*m+59 <= 729*3^n := by omega
  omega

theorem outer_right_budget (n m v E : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= m)
    (hmax : m+3 < 3^n) (hE : E <= 35*n+120)
    (hgap : absDiff v (13*m) <= E) :
    9*m+13+(n+6) <= v /\ 14*m+59 <= 3^(n+6) := by
  have hlarge := min_scale_large n m hn hmin
  have hg := absDiff_le_both v (13*m) E hgap
  have hroom : E+13+(n+6) <= 4*m := by omega
  have hfirst : 9*m+13+(n+6) <= v := by omega
  have hm : m < 3^n := by omega
  have hp := pow_six n
  have hpos : 1 <= 3^n := by exact Nat.one_le_pow n 3 (by decide)
  have hpower : 14*m+59 <= 729*3^n := by omega
  omega

theorem gate_left_budget (n m u E : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= m)
    (hmax : m+3 < 3^n) (hE : E <= 35*n+120)
    (hgap : absDiff (7*m) (4*u) <= E) :
    m+5 <= u /\ 2*u+2*(n+6) <= 5*m+4 /\ m+2 < 3^(n+6) := by
  have hlarge := min_scale_large n m hn hmin
  have hg := absDiff_le_both (7*m) (4*u) E hgap
  have hlower : 7*m <= 4*u+E := hg.1
  have hupper : 4*u <= 7*m+E := hg.2
  have h1 : E+20 <= 3*m := by omega
  have h2 : 2*E+8*(n+6) <= 6*m+16 := by omega
  have hminu : m+5 <= u := by omega
  have hroom : 2*u+2*(n+6) <= 5*m+4 := by omega
  have hp := pow_six n
  have hm : m+2 < 3^n := by omega
  have hpos : 1 <= 3^n := by exact Nat.one_le_pow n 3 (by decide)
  have hpow : 3^n <= 729*3^n := by omega
  omega

theorem gate_right_budget (n m v E : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= m)
    (hmax : m+3 < 3^n) (hE : E <= 35*n+120)
    (hgap : absDiff (7*m) (4*v) <= E) :
    m <= v /\ m < 3^(n+6) /\
    2*v+2*(n+6)+16 <= 5*m /\
    2*v+2*(n+6)+7 <= 4*m := by
  have hlarge := min_scale_large n m hn hmin
  have hg := absDiff_le_both (7*m) (4*v) E hgap
  have hlower : 7*m <= 4*v+E := hg.1
  have hupper : 4*v <= 7*m+E := hg.2
  have hroom1 : 2*E+8*(n+6)+64 <= 6*m := by omega
  have hroom2 : 2*E+8*(n+6)+28 <= 2*m := by omega
  have hmv : m <= v := by omega
  have hpower : m < 3^(n+6) := by
    have hp := pow_six n
    have hpos : 1 <= 3^n := by exact Nat.one_le_pow n 3 (by decide)
    omega
  have hodd : 2*v+2*(n+6)+16 <= 5*m := by omega
  have heven : 2*v+2*(n+6)+7 <= 4*m := by omega
  exact ⟨hmv,hpower,hodd,heven⟩

theorem absDiff_of_int_window (x y W : Nat)
    (hlo : -(W : Int) <= (x : Int)-(y : Int))
    (hhi : (x : Int)-(y : Int) <= W) : absDiff x y <= W := by
  unfold absDiff
  by_cases hxy : x <= y
  · simp [hxy]
    omega
  · simp [hxy]
    omega

theorem far_far_terminal_to_outer (n u v x y B e c : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= v) (hmax : v+3 < 3^n)
    (hB : B <= 9*n+55) (he : e <= 26*n+46) (hc : c <= 9)
    (hterm : absDiff x (4*y) <= B)
    (hbridgeLo : -(e : Int) <= (x : Int)-4*(y : Int)-(c : Int)-((u : Int)-13*(v : Int)))
    (hbridgeHi : (x : Int)-4*(y : Int)-(c : Int)-((u : Int)-13*(v : Int)) <= e) :
    9*v+39+(n+6) <= u /\ 14*v+59 <= 3^(n+6) := by
  have ht := absDiff_le_both x (4*y) B hterm
  have hgapLo : -((B+e+c : Nat) : Int) <= (u : Int)-13*(v : Int) := by omega
  have hgapHi : (u : Int)-13*(v : Int) <= B+e+c := by omega
  have hgap := absDiff_of_int_window u (13*v) (B+e+c) hgapLo hgapHi
  have hE : B+e+c <= 35*n+120 := by omega
  exact outer_left_budget n v u (B+e+c) hn hmin hmax hE hgap

theorem far_near_terminal_to_outer (n u v x y B e c : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= u) (hmax : u+3 < 3^n)
    (hB : B <= 9*n+55) (he : e <= 26*n+46) (hc : c <= 9)
    (hterm : absDiff x (4*y) <= B)
    (hbridgeLo : -(e : Int) <= (x : Int)-4*(y : Int)-(c : Int)-((v : Int)-13*(u : Int)))
    (hbridgeHi : (x : Int)-4*(y : Int)-(c : Int)-((v : Int)-13*(u : Int)) <= e) :
    9*u+13+(n+6) <= v /\ 14*u+59 <= 3^(n+6) := by
  have ht := absDiff_le_both x (4*y) B hterm
  have hgapLo : -((B+e+c : Nat) : Int) <= (v : Int)-13*(u : Int) := by omega
  have hgapHi : (v : Int)-13*(u : Int) <= B+e+c := by omega
  have hgap := absDiff_of_int_window v (13*u) (B+e+c) hgapLo hgapHi
  have hE : B+e+c <= 35*n+120 := by omega
  exact outer_right_budget n u v (B+e+c) hn hmin hmax hE hgap

theorem near_far_terminal_to_gate (n u v x y B e c : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= v) (hmax : v+3 < 3^n)
    (hB : B <= 9*n+55) (he : e <= 14*n+12) (hc : c <= 2)
    (hterm : absDiff y (4*x) <= B)
    (hbridgeLo : -(e : Int) <= (y : Int)-4*(x : Int)-(c : Int)-(7*(v : Int)-4*(u : Int)))
    (hbridgeHi : (y : Int)-4*(x : Int)-(c : Int)-(7*(v : Int)-4*(u : Int)) <= e) :
    v+5 <= u /\ 2*u+2*(n+6) <= 5*v+4 /\ v+2 < 3^(n+6) := by
  have ht := absDiff_le_both y (4*x) B hterm
  have hgapLo : -((B+e+c : Nat) : Int) <= 7*(v : Int)-4*(u : Int) := by omega
  have hgapHi : 7*(v : Int)-4*(u : Int) <= B+e+c := by omega
  have hgap := absDiff_of_int_window (7*v) (4*u) (B+e+c) hgapLo hgapHi
  have hE : B+e+c <= 35*n+120 := by omega
  exact gate_left_budget n v u (B+e+c) hn hmin hmax hE hgap

theorem near_near_terminal_to_gate (n u v x y B e c : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= u) (hmax : u+3 < 3^n)
    (hB : B <= 9*n+55) (he : e <= 14*n+12) (hc : c <= 2)
    (hterm : absDiff y (4*x) <= B)
    (hbridgeLo : -(e : Int) <= (y : Int)-4*(x : Int)-(c : Int)-(7*(u : Int)-4*(v : Int)))
    (hbridgeHi : (y : Int)-4*(x : Int)-(c : Int)-(7*(u : Int)-4*(v : Int)) <= e) :
    u <= v /\ u < 3^(n+6) /\
    2*v+2*(n+6)+16 <= 5*u /\ 2*v+2*(n+6)+7 <= 4*u := by
  have ht := absDiff_le_both y (4*x) B hterm
  have hgapLo : -((B+e+c : Nat) : Int) <= 7*(u : Int)-4*(v : Int) := by omega
  have hgapHi : 7*(u : Int)-4*(v : Int) <= B+e+c := by omega
  have hgap := absDiff_of_int_window (7*u) (4*v) (B+e+c) hgapLo hgapHi
  have hE : B+e+c <= 35*n+120 := by omega
  exact gate_right_budget n u v (B+e+c) hn hmin hmax hE hgap

#print axioms outer_left_budget
#print axioms outer_right_budget
#print axioms gate_left_budget
#print axioms gate_right_budget
#print axioms far_far_terminal_to_outer
#print axioms far_near_terminal_to_outer
#print axioms near_far_terminal_to_gate
#print axioms near_near_terminal_to_gate

end BB6.Agent8RootCancellationBudgetBridge
