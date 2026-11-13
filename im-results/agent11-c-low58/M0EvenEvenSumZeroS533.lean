import M0EvenEvenSumZero
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0SumZeroS533
open BB6.Agent46

private theorem six_parent_reach (x y : Nat)
    (hy : 6≤y) (he : y%2=0)
    (h0 : (x+y)%8≠0) (h7 : (x+y)%8≠7)
    (hr : BB6.Agent3.CReach x y) :
    BB6.Agent3.CReach (x+y-2) ((y-2)/2) :=
  (six_even_right_blank_reach_iff x y hy he h0 h7).mp hr

/-- The B_s branch for s=1024*w+533 has three exact six-even-right
    inverse edges.  Its terminal sum-zero target has one odd-right
    forbidden parent and one even-right parent that reduces in two
    further gates to an odd-right sum-one state. -/
theorem blank_no_B_s533 (w : Nat) :
    ¬ BB6.Agent3.CReach (48024+92160*w) (112590+216064*w) := by
  intro h0
  have h1 : BB6.Agent3.CReach (160612+308224*w) (56294+108032*w) := by
    have hp := six_parent_reach
      (48024+92160*w) (112590+216064*w)
      (by omega) (by omega) (by omega) (by omega) h0
    convert hp using 1 <;> omega
  have h2 : BB6.Agent3.CReach (216904+416256*w) (28146+54016*w) := by
    have hp := six_parent_reach
      (160612+308224*w) (56294+108032*w)
      (by omega) (by omega) (by omega) (by omega) h1
    convert hp using 1 <;> omega
  have h3 : BB6.Agent3.CReach (245048+470272*w) (14072+27008*w) := by
    have hp := six_parent_reach
      (216904+416256*w) (28146+54016*w)
      (by omega) (by omega) (by omega) (by omega) h2
    convert hp using 1 <;> omega
  have hD : ¬ BB6.Agent3.CReach (259118+497280*w) (7035+13504*w) := by
    exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (259118+497280*w) (7035+13504*w)
      (by omega) (by omega) (by omega) (by omega)
  have hE : ¬ BB6.Agent3.CReach (64778+124320*w) (104202+199984*w) := by
    intro hE0
    have hE1 : BB6.Agent3.CReach (168978+324304*w) (52100+99992*w) := by
      have hp := six_parent_reach
        (64778+124320*w) (104202+199984*w)
        (by omega) (by omega) (by omega) (by omega) hE0
      convert hp using 1 <;> omega
    have hE2 : BB6.Agent3.CReach (221076+424296*w) (26049+49996*w) := by
      have hp := six_parent_reach
        (168978+324304*w) (52100+99992*w)
        (by omega) (by omega) (by omega) (by omega) hE1
      convert hp using 1 <;> omega
    exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (221076+424296*w) (26049+49996*w)
      (by omega) (by omega) (by omega) (by omega) hE2
  have hterminal : ¬ BB6.Agent3.CReach (245048+470272*w) (14072+27008*w) :=
    BB6.Agent11M0SumZeroVerified.blank_no_sumzero_target
      (245048+470272*w) (14072+27008*w) (32390+62160*w)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hD hE
  exact hterminal h3

/-- The corresponding A_s target is excluded by the generic source
    sum-zero parent theorem: its L_s parent is the existing mod-8-five
    exclusion and its B_s parent is blank_no_B_s533. -/
theorem blank_no_A_s533 (w : Nat) :
    ¬ BB6.Agent3.CReach (110994+212992*w) (81110+155648*w) := by
  let s := 1024*w+533
  let x := 130+208*s
  let y := 94+152*s
  let S := 28+45*s
  have hD : ¬ BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
    have hL := BB6.Agent11M0SumZeroVerified.blank_no_L_s_mod8_five
      s (by dsimp [s]; omega)
    have hx : x+y-2=222+360*s := by dsimp [x,y]; omega
    have hy : (y-2)/2=46+76*s := by dsimp [y]; omega
    rw [hx,hy]
    exact hL
  have hE : ¬ BB6.Agent3.CReach (2*S-2) ((x+2*y-2*S-8)/2) := by
    have hB := blank_no_B_s533 w
    have hx : 2*S-2=48024+92160*w := by dsimp [S,s]; omega
    have hy : (x+2*y-2*S-8)/2=112590+216064*w := by
      dsimp [x,y,S,s]
      omega
    rw [hx,hy]
    exact hB
  have hxgt : 5<x := by dsimp [x]; omega
  have hxe : x%2=0 := by dsimp [x,s]; omega
  have hyge : 6≤y := by dsimp [y,s]; omega
  have hye : y%2=0 := by dsimp [y,s]; omega
  have hsum : x+y=8*S := by dsimp [x,y,S]; omega
  have hS4 : S%4≠0 := by dsimp [S,s]; omega
  have hSgt : 2<S := by dsimp [S,s]; omega
  have hA := BB6.Agent11M0SumZeroVerified.blank_no_sumzero_target
    x y S hxgt hxe hyge hye hsum hS4 hSgt hD hE
  have hx : 130+208*s=110994+212992*w := by dsimp [s]; omega
  have hy : 94+152*s=81110+155648*w := by dsimp [s]; omega
  change ¬ BB6.Agent3.CReach (130+208*s) (94+152*s) at hA
  simpa only [hx,hy] using hA

/-- New source-exact high-stop cylinder for s=1024*w+533. -/
theorem blank_no_high_stop_s533 (w : Nat) :
    ¬ BB6.Agent3.CReach (68305+131072*w) (102460+196608*w) := by
  intro hr
  have hstart : BB6.Agent3.CReach
      (17+64*(1067+2048*w)) (28+96*(1067+2048*w)) := by
    convert hr using 1 <;> omega
  have hA := BB6.Agent11M0SumZeroVerified.mzero_first_two_reach
    (1067+2048*w) hstart
  have hA' : BB6.Agent3.CReach
      (110994+212992*w) (81110+155648*w) := by
    convert hA using 1 <;> omega
  exact blank_no_A_s533 w hA'

#print axioms blank_no_B_s533
#print axioms blank_no_A_s533
#print axioms blank_no_high_stop_s533
end BB6.Agent11M0SumZeroS533
