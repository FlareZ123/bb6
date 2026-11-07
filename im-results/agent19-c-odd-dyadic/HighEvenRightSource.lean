import EvenRightSixOrbit
import HighEvenRightArithmetic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19HighEvenRight
open BB6.Agent46

/-- Every high stopping target in this residue class has a unique
    even-right predecessor, whose odd-right coordinate and sum violate
    the genuine blank-orbit image invariant. -/
theorem high_even_right_blank_unreachable (j m : Nat)
    (hm : 3≤m) (hm4 : m%4=3) (hj8 : j%8=(m+3)%8) :
    ¬ BB6.Agent3.CReach (2*j+3) (highK j m) := by
  obtain ⟨hk2,hk6,hxk8,hy5,hyodd,hsum4⟩ :=
    high_even_right_parent_arithmetic j m hm hm4 hj8
  intro hr
  have hparent :
      BB6.Agent3.CReach (2*j+3+highK j m-2)
        ((highK j m-2)/2) :=
    (BB6.Agent46.six_even_right_blank_reach_iff
      (2*j+3) (highK j m) hk6 hk2 (by omega) (by omega)).mp hr
  rcases hparent with ⟨time,hrun⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hrun
      omega
  | succ n =>
      have himage := BB6.Agent3.blank_section_odd_image n
        (2*j+3+highK j m-2) ((highK j m-2)/2) hrun hy5 hyodd
      omega

#print axioms high_even_right_blank_unreachable
end BB6.Agent19HighEvenRight
