import M0EvenEvenSumZeroS31
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0SumZeroS31W1
open BB6.Agent46

private theorem six_parent_reach (x y : Nat)
    (hy : 6≤y) (he : y%2=0)
    (h0 : (x+y)%8≠0) (h7 : (x+y)%8≠7)
    (hr : BB6.Agent3.CReach x y) :
    BB6.Agent3.CReach (x+y-2) ((y-2)/2) :=
  (six_even_right_blank_reach_iff x y hy he h0 h7).mp hr

/-- For w=1 mod 4, the bounce parent of L_s (s=32*w+31) is
    excluded by four six-even-right edges and the odd-right sum-one image.
    If L_s is blank-reached, its direct parent chain therefore forces
    reachability of the explicit even-even residual R below. This is a
    reduction, not an exclusion of L_s or of the high-stop root. -/
theorem l_s31_w1mod4_parent_reduction (z : Nat)
    (hL : BB6.Agent3.CReach
      (11382+11520*(4*z+1)) (2402+2432*(4*z+1))) :
    BB6.Agent3.CReach
      (7034+7130*(4*z+1)) (4563+4627*(4*z+1)) := by
  let w := 4*z+1
  have hw : w=4*z+1 := rfl
  let x := 11382+11520*w
  let y := 2402+2432*w
  let S := 1723+1744*w
  have hx0 : 0<x := by dsimp [x]; omega
  have hxe : x%2=0 := by dsimp [x]; omega
  have hyge : 6≤y := by dsimp [y]; omega
  have hye : y%2=0 := by dsimp [y]; omega
  have hsum : x+y=8*S := by dsimp [x,y,S]; omega
  have hS4 : S%4≠0 := by dsimp [S]; omega
  have hSgt : 2<S := by dsimp [S]; omega
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent3.cReach_parent_of_left_gt5 x y hx0 hL
  have hparents := BB6.Agent11M0SumZeroVerified.even_even_sumzero_parent
    a k x y S hx0 hxe hyge hye hsum hS4 hSgt hstep
  rcases hparents with hD | hE
  · rcases hD with ⟨ha,hk⟩
    have hxD : x+y-2=13782+13952*w := by dsimp [x,y]; omega
    have hyD : (y-2)/2=1200+1216*w := by dsimp [y]; omega
    rw [ha,hk,hxD,hyD] at hprev
    have hD1 := six_parent_reach
      (13782+13952*w) (1200+1216*w)
      (by omega) (by omega) (by omega) (by omega) hprev
    have hD1' : BB6.Agent3.CReach
        (14980+15168*w) (599+608*w) := by
      have hx : (13782+13952*w)+(1200+1216*w)-2 =
          14980+15168*w := by omega
      have hy : ((1200+1216*w)-2)/2=599+608*w := by omega
      simpa only [hx,hy] using hD1
    have hD2 := (BB6.Agent3.evenodd_four_blank_reach_iff
      (14980+15168*w) (599+608*w)
      (by omega) (by omega) (by omega) (by omega)).mp hD1'
    have hD2' : BB6.Agent3.CReach
        (7787+7888*w) (4192+4248*w) := by
      have hx : ((14980+15168*w)+(599+608*w)-5)/2 =
          7787+7888*w := by omega
      have hy : ((14980+15168*w)+3*(599+608*w)-9)/4 =
          4192+4248*w := by omega
      simpa only [hx,hy] using hD2
    have hD3 := six_parent_reach
      (7787+7888*w) (4192+4248*w)
      (by omega) (by omega) (by omega) (by omega) hD2'
    have hD3' : BB6.Agent3.CReach
        (11977+12136*w) (2095+2124*w) := by
      have hx : (7787+7888*w)+(4192+4248*w)-2 =
          11977+12136*w := by omega
      have hy : ((4192+4248*w)-2)/2=2095+2124*w := by omega
      simpa only [hx,hy] using hD3
    have hD4 := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (11977+12136*w) (2095+2124*w)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp hD3'
    have hD4' : BB6.Agent3.CReach
        (7034+7130*w) (4563+4627*w) := by
      have hx : ((11977+12136*w)+(2095+2124*w)-4)/2 =
          7034+7130*w := by omega
      have hy : ((11977+12136*w)+3*(2095+2124*w)-10)/4 =
          4563+4627*w := by omega
      simpa only [hx,hy] using hD4
    simpa only [hw] using hD4'
  · rcases hE with ⟨ha,hk⟩
    have hxE : 2*S-2=3444+3488*w := by dsimp [S]; omega
    have hyE : (x+2*y-2*S-8)/2=6366+6448*w := by
      dsimp [x,y,S]
      omega
    rw [ha,hk,hxE,hyE] at hprev
    have hE1 := six_parent_reach
      (3444+3488*w) (6366+6448*w)
      (by omega) (by omega) (by omega) (by omega) hprev
    have hE1' : BB6.Agent3.CReach
        (9808+9936*w) (3182+3224*w) := by
      have hx : (3444+3488*w)+(6366+6448*w)-2 =
          9808+9936*w := by omega
      have hy : ((6366+6448*w)-2)/2=3182+3224*w := by omega
      simpa only [hx,hy] using hE1
    have hE2 := six_parent_reach
      (9808+9936*w) (3182+3224*w)
      (by omega) (by omega) (by omega) (by omega) hE1'
    have hE2' : BB6.Agent3.CReach
        (12988+13160*w) (1590+1612*w) := by
      have hx : (9808+9936*w)+(3182+3224*w)-2 =
          12988+13160*w := by omega
      have hy : ((3182+3224*w)-2)/2=1590+1612*w := by omega
      simpa only [hx,hy] using hE2
    have hE3 := six_parent_reach
      (12988+13160*w) (1590+1612*w)
      (by omega) (by omega) (by omega) (by omega) hE2'
    have hE3' : BB6.Agent3.CReach
        (14576+14772*w) (794+806*w) := by
      have hx : (12988+13160*w)+(1590+1612*w)-2 =
          14576+14772*w := by omega
      have hy : ((1590+1612*w)-2)/2=794+806*w := by omega
      simpa only [hx,hy] using hE3
    have hE4 := six_parent_reach
      (14576+14772*w) (794+806*w)
      (by omega) (by omega) (by omega) (by omega) hE3'
    have hE4' : BB6.Agent3.CReach
        (15368+15578*w) (396+403*w) := by
      have hx : (14576+14772*w)+(794+806*w)-2 =
          15368+15578*w := by omega
      have hy : ((794+806*w)-2)/2=396+403*w := by omega
      simpa only [hx,hy] using hE4
    have hEfalse := BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (15368+15578*w) (396+403*w)
      (by omega) (by omega) (by omega) (by omega)
    exact False.elim (hEfalse hE4')

#print axioms l_s31_w1mod4_parent_reduction
end BB6.Agent11M0SumZeroS31W1
