import M0EvenEvenSumZero
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0SumZeroS293
open BB6.Agent46

private theorem six_parent_reach (x y : Nat)
    (hy : 6≤y) (he : y%2=0)
    (h0 : (x+y)%8≠0) (h7 : (x+y)%8≠7)
    (hr : BB6.Agent3.CReach x y) :
    BB6.Agent3.CReach (x+y-2) ((y-2)/2) :=
  (six_even_right_blank_reach_iff x y hy he h0 h7).mp hr

/-- A new infinite B_s cylinder: s=2048*w+293. Nine exact six-even-right
    inverse edges terminate at an odd-right sum-one state. -/
theorem blank_no_B_s293 (w : Nat) :
    ¬ BB6.Agent3.CReach (26424+184320*w) (61950+432128*w) := by
  intro h0
  have h1 : BB6.Agent3.CReach (88372+616448*w) (30974+216064*w) := by
    have hp := six_parent_reach
      (26424+184320*w) (61950+432128*w)
      (by omega) (by omega) (by omega) (by omega) h0
    convert hp using 1 <;> omega
  have h2 : BB6.Agent3.CReach (119344+832512*w) (15486+108032*w) := by
    have hp := six_parent_reach
      (88372+616448*w) (30974+216064*w)
      (by omega) (by omega) (by omega) (by omega) h1
    convert hp using 1 <;> omega
  have h3 : BB6.Agent3.CReach (134828+940544*w) (7742+54016*w) := by
    have hp := six_parent_reach
      (119344+832512*w) (15486+108032*w)
      (by omega) (by omega) (by omega) (by omega) h2
    convert hp using 1 <;> omega
  have h4 : BB6.Agent3.CReach (142568+994560*w) (3870+27008*w) := by
    have hp := six_parent_reach
      (134828+940544*w) (7742+54016*w)
      (by omega) (by omega) (by omega) (by omega) h3
    convert hp using 1 <;> omega
  have h5 : BB6.Agent3.CReach (146436+1021568*w) (1934+13504*w) := by
    have hp := six_parent_reach
      (142568+994560*w) (3870+27008*w)
      (by omega) (by omega) (by omega) (by omega) h4
    convert hp using 1 <;> omega
  have h6 : BB6.Agent3.CReach (148368+1035072*w) (966+6752*w) := by
    have hp := six_parent_reach
      (146436+1021568*w) (1934+13504*w)
      (by omega) (by omega) (by omega) (by omega) h5
    convert hp using 1 <;> omega
  have h7 : BB6.Agent3.CReach (149332+1041824*w) (482+3376*w) := by
    have hp := six_parent_reach
      (148368+1035072*w) (966+6752*w)
      (by omega) (by omega) (by omega) (by omega) h6
    convert hp using 1 <;> omega
  have h8 : BB6.Agent3.CReach (149812+1045200*w) (240+1688*w) := by
    have hp := six_parent_reach
      (149332+1041824*w) (482+3376*w)
      (by omega) (by omega) (by omega) (by omega) h7
    convert hp using 1 <;> omega
  have h9 : BB6.Agent3.CReach (150050+1046888*w) (119+844*w) := by
    have hp := six_parent_reach
      (149812+1045200*w) (240+1688*w)
      (by omega) (by omega) (by omega) (by omega) h8
    convert hp using 1 <;> omega
  exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    (150050+1046888*w) (119+844*w)
    (by omega) (by omega) (by omega) h9

/-- The corresponding A_s target is excluded by the source-certified
    generic sum-zero parent theorem: its L_s parent is the known mod-8-five
    exclusion, and its B_s parent is blank_no_B_s293. -/
theorem blank_no_A_s293 (w : Nat) :
    ¬ BB6.Agent3.CReach (61074+425984*w) (44630+311296*w) := by
  let s := 2048*w+293
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
    have hB := blank_no_B_s293 w
    have hx : 2*S-2=26424+184320*w := by dsimp [S,s]; omega
    have hy : (x+2*y-2*S-8)/2=61950+432128*w := by
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
  have hx : 130+208*s=61074+425984*w := by dsimp [s]; omega
  have hy : 94+152*s=44630+311296*w := by dsimp [s]; omega
  rw [hx,hy] at hA
  exact hA

/-- New source-exact m=0 high-stop cylinder, pulled back through the
    first two original-section inverse edges. -/
theorem blank_no_high_stop_s293 (w : Nat) :
    ¬ BB6.Agent3.CReach (37585+262144*w) (56380+393216*w) := by
  intro hr
  have hstart : BB6.Agent3.CReach
      (17+64*(587+4096*w)) (28+96*(587+4096*w)) := by
    convert hr using 1 <;> omega
  have hA := BB6.Agent11M0SumZeroVerified.mzero_first_two_reach
    (587+4096*w) hstart
  have hA' : BB6.Agent3.CReach
      (61074+425984*w) (44630+311296*w) := by
    convert hA using 1 <;> omega
  exact blank_no_A_s293 w hA'

#print axioms blank_no_B_s293
#print axioms blank_no_A_s293
#print axioms blank_no_high_stop_s293
end BB6.Agent11M0SumZeroS293
