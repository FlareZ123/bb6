import M0EvenEvenSumZero
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0SumZeroS229
open BB6.Agent46

private theorem six_parent_reach (x y : Nat)
    (hy : 6≤y) (he : y%2=0)
    (h0 : (x+y)%8≠0) (h7 : (x+y)%8≠7)
    (hr : BB6.Agent3.CReach x y) :
    BB6.Agent3.CReach (x+y-2) ((y-2)/2) :=
  (six_even_right_blank_reach_iff x y hy he h0 h7).mp hr

/-- The B_s branch for s=1024*w+229 has five exact six-even-right
    inverse edges.  Its terminal sum-zero state has only two source
    parents, both forbidden by the odd-right image. -/
theorem blank_no_B_s229 (w : Nat) :
    ¬ BB6.Agent3.CReach (20664+92160*w) (48446+216064*w) := by
  intro h0
  have h1 : BB6.Agent3.CReach (69108+308224*w) (24222+108032*w) := by
    have hp := six_parent_reach
      (20664+92160*w) (48446+216064*w)
      (by omega) (by omega) (by omega) (by omega) h0
    convert hp using 1 <;> omega
  have h2 : BB6.Agent3.CReach (93328+416256*w) (12110+54016*w) := by
    have hp := six_parent_reach
      (69108+308224*w) (24222+108032*w)
      (by omega) (by omega) (by omega) (by omega) h1
    convert hp using 1 <;> omega
  have h3 : BB6.Agent3.CReach (105436+470272*w) (6054+27008*w) := by
    have hp := six_parent_reach
      (93328+416256*w) (12110+54016*w)
      (by omega) (by omega) (by omega) (by omega) h2
    convert hp using 1 <;> omega
  have h4 : BB6.Agent3.CReach (111488+497280*w) (3026+13504*w) := by
    have hp := six_parent_reach
      (105436+470272*w) (6054+27008*w)
      (by omega) (by omega) (by omega) (by omega) h3
    convert hp using 1 <;> omega
  have h5 : BB6.Agent3.CReach (114512+510784*w) (1512+6752*w) := by
    have hp := six_parent_reach
      (111488+497280*w) (3026+13504*w)
      (by omega) (by omega) (by omega) (by omega) h4
    convert hp using 1 <;> omega
  have hD : ¬ BB6.Agent3.CReach (116022+517536*w) (755+3376*w) := by
    exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (116022+517536*w) (755+3376*w)
      (by omega) (by omega) (by omega) (by omega)
  have hE : ¬ BB6.Agent3.CReach (29004+129384*w) (44261+197452*w) := by
    exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (29004+129384*w) (44261+197452*w)
      (by omega) (by omega) (by omega) (by omega)
  have hterminal : ¬ BB6.Agent3.CReach (114512+510784*w) (1512+6752*w) :=
    BB6.Agent11M0SumZeroVerified.blank_no_sumzero_target
      (114512+510784*w) (1512+6752*w) (14503+64692*w)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hD hE
  exact hterminal h5

/-- The corresponding A_s target is excluded by the generic source
    sum-zero parent theorem: its L_s parent is the existing mod-8-five
    exclusion and its B_s parent is blank_no_B_s229. -/
theorem blank_no_A_s229 (w : Nat) :
    ¬ BB6.Agent3.CReach (47762+212992*w) (34902+155648*w) := by
  let s := 1024*w+229
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
    have hB := blank_no_B_s229 w
    have hx : 2*S-2=20664+92160*w := by dsimp [S,s]; omega
    have hy : (x+2*y-2*S-8)/2=48446+216064*w := by
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
  have hx : 130+208*s=47762+212992*w := by dsimp [s]; omega
  have hy : 94+152*s=34902+155648*w := by dsimp [s]; omega
  change ¬ BB6.Agent3.CReach (130+208*s) (94+152*s) at hA
  simpa only [hx,hy] using hA

/-- New source-exact high-stop cylinder for s=1024*w+229. -/
theorem blank_no_high_stop_s229 (w : Nat) :
    ¬ BB6.Agent3.CReach (29393+131072*w) (44092+196608*w) := by
  intro hr
  have hstart : BB6.Agent3.CReach
      (17+64*(459+2048*w)) (28+96*(459+2048*w)) := by
    convert hr using 1 <;> omega
  have hA := BB6.Agent11M0SumZeroVerified.mzero_first_two_reach
    (459+2048*w) hstart
  have hA' : BB6.Agent3.CReach
      (47762+212992*w) (34902+155648*w) := by
    convert hA using 1 <;> omega
  exact blank_no_A_s229 w hA'

#print axioms blank_no_B_s229
#print axioms blank_no_A_s229
#print axioms blank_no_high_stop_s229
end BB6.Agent11M0SumZeroS229
