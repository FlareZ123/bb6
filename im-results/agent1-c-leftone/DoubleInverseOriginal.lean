import SectionAffineInverse
import OddFourExactOriginal
import Agent3CImage
import SectionRightOne
import Lean.Elab.Tactic.Omega

namespace BB6.Agent1CDoubleInverse
open BB6.Agent46

/-- A parameter-uniform double-inverse obstruction for the authentic
    Machine C blank section. Here r is the target right-counter quarter.
    The arithmetic congruence certifies that the unique first parent has
    a unique odd-four parent in the forbidden odd-right image sector. -/
theorem no_double_inverse_target (x r : Nat)
    (hx : x%4=1) (hr : 3≤r) (hmod : (3*x+22*r)%16=1) :
    ¬ BB6Agent34.CReach x (4*r) := by
  rintro ⟨time,ht⟩
  cases time with
  | zero => simp [BB6.Agent8Section.run] at ht; omega
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at ht
      | some p =>
          rcases p with ⟨a,k⟩
          have hnext : secNext (a,k)=some (x,4*r) := by
            simpa [BB6.Agent8Section.run,hp] using ht
          obtain ⟨ha,hk⟩ :=
            (BB6.Agent15.section_sum_one_even_iff_affine a k x (4*r)
              (by omega) (by omega) (by omega)).mp hnext
          have hparent : BB6Agent34.CReach (x+4*r-2) (2*r-1) := by
            refine ⟨n,?_⟩
            have ha' : a=x+4*r-2 := ha
            have hk' : k=2*r-1 := by omega
            simpa only [ha',hk'] using hp
          have hpar_x : (x+4*r-2)%2=1 := by omega
          have hpar_y : (2*r-1)%2=1 := by omega
          have hpar_big : 5≤2*r-1 := by omega
          have hpar_four : ((x+4*r-2)+(2*r-1))%8=4 := by omega
          obtain ⟨b,c,⟨m,hm⟩,hb,hc⟩ :=
            (BB6Agent34.odd_four_reach_iff (x+4*r-2) (2*r-1)
              hpar_x hpar_y hpar_big hpar_four).mp hparent
          have hodd : c%2=1 := by omega
          have hbig : 5≤c := by omega
          have hbad : (b+c)%4=1 := by omega
          cases m with
          | zero => simp [BB6.Agent8Section.run] at hm; omega
          | succ t =>
              have hi := BB6.Agent3.blank_section_odd_image t b c hm hbig hodd
              omega

/-- Three of the four whole two-dimensional forbidden cylinders. -/
theorem blank_no_one_twenty (u v : Nat) :
    ¬ BB6Agent34.CReach (16*u+1) (32*v+20) := by
  have hh := no_double_inverse_target (16*u+1) (8*v+5)
    (by omega) (by omega) (by omega)
  simpa [show 4*(8*v+5)=32*v+20 by omega] using hh

theorem blank_no_five_twelve (u v : Nat) :
    ¬ BB6Agent34.CReach (16*u+5) (32*v+12) := by
  have hh := no_double_inverse_target (16*u+5) (8*v+3)
    (by omega) (by omega) (by omega)
  simpa [show 4*(8*v+3)=32*v+12 by omega] using hh

theorem blank_no_thirteen_twenty_eight (u v : Nat) :
    ¬ BB6Agent34.CReach (16*u+13) (32*v+28) := by
  have hh := no_double_inverse_target (16*u+13) (8*v+7)
    (by omega) (by omega) (by omega)
  simpa [show 4*(8*v+7)=32*v+28 by omega] using hh

/-- The low y=4 slice is covered by the original right-one uniqueness. -/
theorem blank_no_nine_four_base (u : Nat) :
    ¬ BB6Agent34.CReach (16*u+9) 4 := by
  rintro ⟨time,ht⟩
  cases time with
  | zero => simp [BB6.Agent8Section.run] at ht
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at ht
      | some p =>
          rcases p with ⟨a,k⟩
          have hnext : secNext (a,k)=some (16*u+9,4) := by
            simpa [BB6.Agent8Section.run,hp] using ht
          obtain ⟨ha,hk⟩ :=
            (BB6.Agent15.section_sum_one_even_iff_affine a k (16*u+9) 4
              (by omega) (by omega) (by omega)).mp hnext
          have hparent : BB6.Agent8Section.run secNext n (some (5,1)) =
              some (16*u+11,1) := by
            have ha' : a=16*u+11 := by omega
            have hk' : k=1 := by omega
            simpa only [ha',hk'] using hp
          have hright := Agent20Gate.blank_right_one_iff_initial n (16*u+11) hparent
          omega

theorem blank_no_nine_four (u v : Nat) :
    ¬ BB6Agent34.CReach (16*u+9) (32*v+4) := by
  cases v with
  | zero => simpa using blank_no_nine_four_base u
  | succ v =>
      have hh := no_double_inverse_target (16*u+9) (8*(v+1)+1)
        (by omega) (by omega) (by omega)
      simpa [show 4*(8*(v+1)+1)=32*(v+1)+4 by omega] using hh

#print axioms no_double_inverse_target
#print axioms blank_no_one_twenty
#print axioms blank_no_five_twelve
#print axioms blank_no_thirteen_twenty_eight
#print axioms blank_no_nine_four
end BB6.Agent1CDoubleInverse
