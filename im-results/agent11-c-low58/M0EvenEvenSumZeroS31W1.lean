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

/-- The L_s parent for s=32*w+31 is blank-unreachable on the
    w=1 mod 4 cylinder. Its direct parent passes through an even/odd-four
    edge and an odd/odd low-valuation edge to an odd-right sum-two state.
    Its bounce parent passes through four six-even-right edges to an
    odd-right sum-one state. -/
theorem blank_no_L_s31_w1mod4 (z : Nat) :
    ¬ BB6.Agent3.CReach
      (11382+11520*(4*z+1)) (2402+2432*(4*z+1)) := by
  let w := 4*z+1
  have hw : w=4*z+1 := rfl
  let x := 11382+11520*w
  let y := 2402+2432*w
  let S := 1723+1744*w
  have hD : ¬ BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
    intro hr
    have hD0 : BB6.Agent3.CReach
        (13782+13952*w) (1200+1216*w) := by
      have hx : x+y-2=13782+13952*w := by dsimp [x,y]; omega
      have hy : (y-2)/2=1200+1216*w := by dsimp [y]; omega
      simpa only [hx,hy] using hr
    have hD1 := six_parent_reach
      (13782+13952*w) (1200+1216*w)
      (by omega) (by omega) (by omega) (by omega) hD0
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
    exact BB6.Agent11High.blank_no_odd_sum_two
      (7034+7130*w) (4563+4627*w)
      (by omega) (by omega) (by omega) hD4'
  have hE : ¬ BB6.Agent3.CReach
      (2*S-2) ((x+2*y-2*S-8)/2) := by
    intro hr
    have hE0 : BB6.Agent3.CReach
        (3444+3488*w) (6366+6448*w) := by
      have hx : 2*S-2=3444+3488*w := by dsimp [S]; omega
      have hy : (x+2*y-2*S-8)/2=6366+6448*w := by
        dsimp [x,y,S]
        omega
      simpa only [hx,hy] using hr
    have hE1 := six_parent_reach
      (3444+3488*w) (6366+6448*w)
      (by omega) (by omega) (by omega) (by omega) hE0
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
    exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (15368+15578*w) (396+403*w)
      (by omega) (by omega) (by omega) (by omega) hE4'
  change ¬ BB6.Agent3.CReach x y
  exact BB6.Agent11M0SumZeroVerified.blank_no_sumzero_target
    x y S (by dsimp [x]; omega) (by dsimp [x]; omega)
    (by dsimp [y]; omega) (by dsimp [y]; omega)
    (by dsimp [x,y,S]; omega) (by dsimp [S]; omega)
    (by dsimp [S]; omega) hD hE

/-- The A_s target for s=32*w+31 is blank-unreachable when w=1 mod 4:
    its two sum-zero parents are the just-excluded L_s cylinder and the
    already source-excluded B_s cylinder. -/
theorem blank_no_A_s31_w1mod4 (z : Nat) :
    ¬ BB6.Agent3.CReach (13234+26624*z) (9670+19456*z) := by
  let w := 4*z+1
  let s := 32*w+31
  let x := 130+208*s
  let y := 94+152*s
  let S := 28+45*s
  have hD : ¬ BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
    have hL := blank_no_L_s31_w1mod4 z
    have hx : x+y-2=222+360*s := by dsimp [x,y]; omega
    have hy : (y-2)/2=46+76*s := by dsimp [y]; omega
    have hxL : 222+360*s=11382+11520*w := by dsimp [s]; omega
    have hyL : 46+76*s=2402+2432*w := by dsimp [s]; omega
    rw [hx,hy,hxL,hyL]
    exact hL
  have hE : ¬ BB6.Agent3.CReach
      (2*S-2) ((x+2*y-2*S-8)/2) := by
    have hB := BB6.Agent11M0SumZeroS31.blank_no_B_s31 w
    have hx : 2*S-2=54+90*s := by dsimp [S]; omega
    have hy : (x+2*y-2*S-8)/2=127+211*s := by
      dsimp [x,y,S]
      omega
    have hxB : 54+90*s=2844+2880*w := by dsimp [s]; omega
    have hyB : 127+211*s=6668+6752*w := by dsimp [s]; omega
    rw [hx,hy,hxB,hyB]
    exact hB
  have hA := BB6.Agent11M0SumZeroVerified.blank_no_sumzero_target
    x y S (by dsimp [x]; omega) (by dsimp [x]; omega)
    (by dsimp [y]; omega) (by dsimp [y]; omega)
    (by dsimp [x,y,S]; omega) (by dsimp [S,s,w]; omega)
    (by dsimp [S]; omega) hD hE
  have hxA : x=13234+26624*z := by dsimp [x,s,w]; omega
  have hyA : y=9670+19456*z := by dsimp [y,s,w]; omega
  simpa only [hxA,hyA] using hA

/-- New m=0 high-stop cylinder: t=(j-7)/32=127 mod 256,
    equivalently j=4071 mod 8192. -/
theorem high_stop_mzero_s31_w1mod4 (j k : Nat)
    (hj : j%8192=4071)
    (hstop : k+j+5=4*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  let z := (j-4071)/8192
  have hjform : j=4071+8192*z := by dsimp [z]; omega
  have hkform : k=12220+24576*z := by rw [hjform] at hstop; omega
  have hxform : 2*j+3=8145+16384*z := by rw [hjform]; omega
  intro hr
  have hr' : BB6.Agent3.CReach
      (8145+16384*z) (12220+24576*z) := by
    simpa only [hxform,hkform] using hr
  have hstart : BB6.Agent3.CReach
      (17+64*(256*z+127)) (28+96*(256*z+127)) := by
    convert hr' using 1 <;> omega
  have hA := BB6.Agent11M0SumZeroVerified.mzero_first_two_reach
    (256*z+127) hstart
  have hA' : BB6.Agent3.CReach
      (13234+26624*z) (9670+19456*z) := by
    convert hA using 1 <;> omega
  exact blank_no_A_s31_w1mod4 z hA'

#print axioms blank_no_L_s31_w1mod4
#print axioms blank_no_A_s31_w1mod4
#print axioms high_stop_mzero_s31_w1mod4
end BB6.Agent11M0SumZeroS31W1
