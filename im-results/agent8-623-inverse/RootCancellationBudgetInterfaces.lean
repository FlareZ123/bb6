import Agent8RootCancellationBudgetBridge
import Agent8LogParentSource
import Agent8GateCompleteSource
import Lean.Elab.Tactic.Omega

/-!
# Direct interface from terminal/root-ray cancellation to existing safety budgets

This module composes the conditional arithmetic bridge with the exact
`logOuterBudget` and `gateBudget` predicates already consumed by the
source two-step repulsion theorems. It does not prove the needed source
exponent transfer or any blank-root nonhalting conclusion.
-/

namespace BB6.Agent8RootCancellationBudgetInterfaces

open BB6.Agent8RootCancellationBudgetBridge
open BB6.Agent8LogParentSource
open BB6.Agent8GateCompleteSource

/-- The left outer-log inequalities imply the existing log-parent predicate,
with parity handled by choosing the stronger odd/even branch. -/
theorem outer_left_to_logOuterBudget (n m u : Nat)
    (hfirst : 9*m+39+(n+6) <= u)
    (hpower : 14*m+59 <= 3^(n+6)) :
    logOuterBudget u m (n+6) := by
  unfold logOuterBudget
  by_cases hm : m%2=1
  · exact Or.inl ⟨hm,hfirst,hpower⟩
  · have hm0 : m%2=0 := by omega
    exact Or.inr (Or.inl ⟨hm0,by omega,by omega⟩)

/-- The right outer-log inequalities imply the existing log-parent predicate,
with parity handled by choosing the stronger odd/even branch. -/
theorem outer_right_to_logOuterBudget (n m v : Nat)
    (hfirst : 9*m+13+(n+6) <= v)
    (hpower : 14*m+59 <= 3^(n+6)) :
    logOuterBudget m v (n+6) := by
  unfold logOuterBudget
  by_cases hv : v%2=1
  · exact Or.inr (Or.inr (Or.inl ⟨hv,by omega,by omega⟩))
  · have hv0 : v%2=0 := by omega
    exact Or.inr (Or.inr (Or.inr ⟨hv0,by omega,by omega⟩))

/-- The left gate inequalities plus the retained root-band upper bound
imply the existing five-branch gate predicate. -/
theorem gate_left_to_gateBudget (n m u : Nat)
    (hfirst : m+5 <= u)
    (hroom : 2*u+2*(n+6) <= 5*m+4)
    (hpower : m+2 < 3^(n+6))
    (hroot : m+3 < 3^n) :
    gateBudget u m (n+6) := by
  unfold gateBudget
  have hpowN : 3^n <= 3^(n+6) :=
    Nat.pow_le_pow_right (by decide : 0<3) (by omega)
  have hroot' : m+3 < 3^(n+6) := lt_of_lt_of_le hroot hpowN
  by_cases hm : m%2=1
  · exact Or.inr (Or.inl ⟨hm,hfirst,hroot',by omega⟩)
  · have hm0 : m%2=0 := by omega
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hm0,by omega,hpower,hroom⟩)))

/-- The right gate inequalities imply the existing five-branch gate
predicate, with parity handled by choosing the appropriate right branch. -/
theorem gate_right_to_gateBudget (n m v : Nat)
    (hfirst : m <= v)
    (hpower : m < 3^(n+6))
    (hroomOdd : 2*v+2*(n+6)+16 <= 5*m)
    (hroomEven : 2*v+2*(n+6)+7 <= 4*m) :
    gateBudget m v (n+6) := by
  unfold gateBudget
  by_cases hv : v%2=1
  · exact Or.inl ⟨hv,by omega,by omega,hroomOdd⟩
  · have hv0 : v%2=0 := by omega
    exact Or.inr (Or.inr (Or.inl ⟨hv0,hfirst,hpower,hroomEven⟩))

/-- Far terminal / far previous ray: the previous state is in the
existing outer-log two-step safety budget. -/
theorem far_far_terminal_to_logOuterBudget (n u v x y B e c : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= v) (hmax : v+3 < 3^n)
    (hB : B <= 9*n+55) (he : e <= 26*n+46) (hc : c <= 9)
    (hterm : absDiff x (4*y) <= B)
    (hbridgeLo : -(e : Int) <=
      (x : Int)-4*(y : Int)-(c : Int)-((u : Int)-13*(v : Int)))
    (hbridgeHi :
      (x : Int)-4*(y : Int)-(c : Int)-((u : Int)-13*(v : Int)) <= e) :
    logOuterBudget u v (n+6) := by
  have h := far_far_terminal_to_outer n u v x y B e c
    hn hmin hmax hB he hc hterm hbridgeLo hbridgeHi
  exact outer_left_to_logOuterBudget n v u h.1 h.2

/-- Far terminal / near previous ray: the previous state is in the
existing outer-log two-step safety budget. -/
theorem far_near_terminal_to_logOuterBudget (n u v x y B e c : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= u) (hmax : u+3 < 3^n)
    (hB : B <= 9*n+55) (he : e <= 26*n+46) (hc : c <= 9)
    (hterm : absDiff x (4*y) <= B)
    (hbridgeLo : -(e : Int) <=
      (x : Int)-4*(y : Int)-(c : Int)-((v : Int)-13*(u : Int)))
    (hbridgeHi :
      (x : Int)-4*(y : Int)-(c : Int)-((v : Int)-13*(u : Int)) <= e) :
    logOuterBudget u v (n+6) := by
  have h := far_near_terminal_to_outer n u v x y B e c
    hn hmin hmax hB he hc hterm hbridgeLo hbridgeHi
  exact outer_right_to_logOuterBudget n u v h.1 h.2

/-- Near terminal / far previous ray: the previous state is in the
existing gate two-step safety budget. -/
theorem near_far_terminal_to_gateBudget (n u v x y B e c : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= v) (hmax : v+3 < 3^n)
    (hB : B <= 9*n+55) (he : e <= 14*n+12) (hc : c <= 2)
    (hterm : absDiff y (4*x) <= B)
    (hbridgeLo : -(e : Int) <=
      (y : Int)-4*(x : Int)-(c : Int)-(7*(v : Int)-4*(u : Int)))
    (hbridgeHi :
      (y : Int)-4*(x : Int)-(c : Int)-(7*(v : Int)-4*(u : Int)) <= e) :
    gateBudget u v (n+6) := by
  have h := near_far_terminal_to_gate n u v x y B e c
    hn hmin hmax hB he hc hterm hbridgeLo hbridgeHi
  exact gate_left_to_gateBudget n v u h.1 h.2.1 h.2.2 hmax

/-- Near terminal / near previous ray: the previous state is in the
existing gate two-step safety budget. -/
theorem near_near_terminal_to_gateBudget (n u v x y B e c : Nat)
    (hn : 10 <= n) (hmin : 3^(n-1)-3 <= u) (hmax : u+3 < 3^n)
    (hB : B <= 9*n+55) (he : e <= 14*n+12) (hc : c <= 2)
    (hterm : absDiff y (4*x) <= B)
    (hbridgeLo : -(e : Int) <=
      (y : Int)-4*(x : Int)-(c : Int)-(7*(u : Int)-4*(v : Int)))
    (hbridgeHi :
      (y : Int)-4*(x : Int)-(c : Int)-(7*(u : Int)-4*(v : Int)) <= e) :
    gateBudget u v (n+6) := by
  have h := near_near_terminal_to_gate n u v x y B e c
    hn hmin hmax hB he hc hterm hbridgeLo hbridgeHi
  exact gate_right_to_gateBudget n u v h.1 h.2.1 h.2.2.1 h.2.2.2

#print axioms outer_left_to_logOuterBudget
#print axioms outer_right_to_logOuterBudget
#print axioms gate_left_to_gateBudget
#print axioms gate_right_to_gateBudget
#print axioms far_far_terminal_to_logOuterBudget
#print axioms far_near_terminal_to_logOuterBudget
#print axioms near_far_terminal_to_gateBudget
#print axioms near_near_terminal_to_gateBudget

end BB6.Agent8RootCancellationBudgetInterfaces
