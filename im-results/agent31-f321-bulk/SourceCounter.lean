import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent31F321Density

/-- The five nonhalting branches of the published F321 two-counter return map.
    Halt is precisely the absent guard a=d+1. -/
inductive CounterMove : Nat → Nat → Nat → Nat → Prop where
 | high (a d:Nat) (h:d+2≤a) :
     CounterMove a d (a-d-2) (2*d+3)
 | equal (a:Nat) :
     CounterMove a a (2*a+4) 1
 | far (a d:Nat) (h1:a<d) (h2:3*a+1≤d) :
     CounterMove a d (4*a+6) (d-3*a)
 | middleEven (a d:Nat) (h1:a<d) (h2:d<3*a+1) (hp:(d-a)%2=0) :
     CounterMove a d (4*a+6) 2
 | middleOdd (a d:Nat) (h1:a<d) (h2:d<3*a+1) (hp:(d-a)%2=1) :
     CounterMove a d (4*a+6) 1

/-- Every live counter transition strictly increases parameter sum. -/
theorem counter_sum_strict
 {a d A D:Nat} (h:CounterMove a d A D):a+d<A+D := by
 cases h with
 | high hg => omega
 | equal => omega
 | far h1 h2 => omega
 | middleEven h1 h2 hp => omega
 | middleOdd h1 h2 hp => omega

/-- Exact inverse classification at outputs with second coordinate at least 3. -/
theorem large_second_only_high_far
 {a d A D:Nat} (h:CounterMove a d A D) (hD:3≤D):
 (a=A+d+2 ∧ D=2*d+3) ∨ (A=4*a+6 ∧ d=D+3*a) := by
 cases h with
 | high hg => left; omega
 | equal => omega
 | far h1 h2 => right; omega
 | middleEven h1 h2 hp => omega
 | middleOdd h1 h2 hp => omega

/-- Convert literal source-map branches into the integer equations used by
    the kernel proof of the odd-coefficient inverse-word congruence. -/
theorem high_far_integral_equations
 {a d A D:Nat} (h:CounterMove a d A D) (hD:3≤D):
  (2*(a:Int)=2*(A:Int)+(D:Int)+1 ∧ 2*(d:Int)=(D:Int)-3) ∨
  (4*(a:Int)=(A:Int)-6 ∧ (d:Int)=(D:Int)+3*(a:Int)) := by
 rcases large_second_only_high_far h hD with hh | hf
 · left
   omega
 · right
   omega

#print axioms counter_sum_strict
#print axioms high_far_integral_equations
end BB6.Agent31F321Density
