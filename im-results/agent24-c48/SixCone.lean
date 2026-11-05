import EvenRightSixOrbit
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- A two-dimensional, all-time structural nonreachability criterion:
    uniquely force the even-right output to an odd-right parent whose
    counter sum violates the authentic blank-section image theorem. -/
theorem six_even_right_bad_parent (x y : Nat)
    (hy : 12≤y) (hdiv : y%4=0)
    (h0 : (x+y)%8≠0) (h7 : (x+y)%8≠7)
    (hbad : ((x+y-2)+((y-2)/2))%4=1 ∨
            ((x+y-2)+((y-2)/2))%4=2) :
    ¬ BB6.Agent3.CReach x y := by
  intro hr
  obtain ⟨time,ht⟩ :=
    (six_even_right_blank_reach_iff x y
      (by omega) (by omega) h0 h7).mp hr
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n
        (x+y-2) ((y-2)/2) ht (by omega) (by omega)
      omega

/-- Source-only proof of an all-parameter forbidden cylinder previously
    approached by finite quotient methods, now without any graph closure. -/
theorem six_cone_seven_four (u v : Nat) (hv : 1≤v) :
    ¬ BB6.Agent3.CReach (8*u+7) (8*v+4) := by
  apply six_even_right_bad_parent (8*u+7) (8*v+4)
  · omega
  · omega
  · omega
  · omega
  · right
    omega

theorem six_cone_two_four (u v : Nat) (hv : 1≤v) :
    ¬ BB6.Agent3.CReach (8*u+2) (8*v+4) := by
  apply six_even_right_bad_parent (8*u+2) (8*v+4)
  · omega
  · omega
  · omega
  · omega
  · left
    omega

theorem six_cone_six_four (u v : Nat) (hv : 1≤v) :
    ¬ BB6.Agent3.CReach (8*u+6) (8*v+4) := by
  apply six_even_right_bad_parent (8*u+6) (8*v+4)
  · omega
  · omega
  · omega
  · omega
  · left
    omega

theorem six_cone_four_zero (u v : Nat) (hv : 2≤v) :
    ¬ BB6.Agent3.CReach (8*u+4) (8*v) := by
  apply six_even_right_bad_parent (8*u+4) (8*v)
  · omega
  · omega
  · omega
  · omega
  · left
    omega

#print axioms six_even_right_bad_parent
#print axioms six_cone_seven_four
#print axioms six_cone_two_four
#print axioms six_cone_six_four
#print axioms six_cone_four_zero

end BB6.Agent46
