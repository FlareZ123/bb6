import OddOddVal3Orbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Full original-source inversion in the odd/odd quadrant whenever the
    sum is positive, divisible by 4, and *not* divisible by 16.
    Exact arithmetic, no recursion-depth bound. -/
theorem oddodd_lowval_parent_iff (a k x y : Nat)
    (hx : x%2=1) (hy : y%2=1) (hy5 : 5≤y)
    (h4 : (x+y)%4=0) (h16 : (x+y)%16≠0)
    (hsize : 24≤x+y) :
    secNext (a,k)=some (x,y) ↔
       x+y=2*a+4 ∧ x+3*y=4*k+10 := by
  by_cases hv2 : (x+y)%8=4
  · exact oddodd_parent_iff a k x y hx hy hy5 hv2
  · have hv3 : (x+y)%16=8 := by omega
    exact oddodd_val3_parent_iff a k x y hx hy hy5 hv3 hsize

/-- The universal true-blank predecessor equivalence for this full
    union of both low 2-adic output layers. -/
theorem oddodd_lowval_blank_reach_iff (x y : Nat)
    (hx : x%2=1) (hy : y%2=1) (hy5 : 5≤y)
    (h4 : (x+y)%4=0) (h16 : (x+y)%16≠0)
    (hsize : 24≤x+y) :
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (x,y)) ↔
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=
      some ((x+y-4)/2,(x+3*y-10)/4)) := by
  by_cases hv2 : (x+y)%8=4
  · exact oddodd_blank_reach_iff x y hx hy hy5 hv2
  · have hv3 : (x+y)%16=8 := by omega
    exact oddodd_val3_blank_reach_iff x y hx hy hy5 hv3 hsize

/-- Arithmetic exact mass difference along all these original-source
    edges: in the a+2*k rank, every inverse edge removes seven units. -/
theorem oddodd_lowval_parent_mass (a k x y : Nat)
    (hx : x%2=1) (hy : y%2=1) (hy5 : 5≤y)
    (h4 : (x+y)%4=0) (h16 : (x+y)%16≠0)
    (hsize : 24≤x+y)
    (hedge : secNext (a,k)=some (x,y)) :
    a+2*k+7=x+2*y := by
  have h := (oddodd_lowval_parent_iff a k x y hx hy hy5 h4 h16 hsize).mp hedge
  omega

#print axioms oddodd_lowval_parent_iff
#print axioms oddodd_lowval_blank_reach_iff
#print axioms oddodd_lowval_parent_mass
end BB6.Agent3
