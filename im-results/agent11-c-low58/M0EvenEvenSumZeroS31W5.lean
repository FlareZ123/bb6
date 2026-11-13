import M0EvenEvenSumZeroS31
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 4096

namespace BB6.Agent11M0SumZeroS31W5
open BB6.Agent46

private theorem div_two_eq (n m : Nat) (h : n=2*m) : n/2=m := by
  rw [h]
  exact Nat.mul_div_cancel_left _ (by omega)

private theorem div_four_eq (n m : Nat) (h : n=4*m) : n/4=m := by
  rw [h]
  exact Nat.mul_div_cancel_left _ (by omega)

private theorem l_direct_y (q : Nat) :
    (2402+2432*(16*q+5))-2 =
      2*(1200+1216*(16*q+5)) := by omega

private theorem root_start_y (q : Nat) :
    28+96*(1024*q+383)=36796+98304*q := by omega

private theorem root_final_y (q : Nat) :
    18+76*(1024*q+383)=29126+77824*q := by omega

private theorem r_to_r1_y (q : Nat) :
    (4563+4627*(16*q+5))-2=2*(13848+37016*q) := by omega

private theorem six_parent_reach (x y : Nat)
    (hy : 6≤y) (he : y%2=0)
    (h0 : (x+y)%8≠0) (h7 : (x+y)%8≠7)
    (hr : BB6.Agent3.CReach x y) :
    BB6.Agent3.CReach (x+y-2) ((y-2)/2) :=
  (six_even_right_blank_reach_iff x y hy he h0 h7).mp hr

private theorem d0_to_d1 (w : Nat) :
    BB6.Agent3.CReach (13782+13952*w) (1200+1216*w) →
    BB6.Agent3.CReach (14980+15168*w) (599+608*w) := by
  intro hr
  have h := six_parent_reach
    (13782+13952*w) (1200+1216*w)
    (by omega) (by omega) (by omega) (by omega) hr
  have hx : (13782+13952*w)+(1200+1216*w)-2=14980+15168*w := by omega
  have hy : ((1200+1216*w)-2)/2=599+608*w :=
    div_two_eq ((1200+1216*w)-2) (599+608*w) (by omega)
  simpa only [hx,hy] using h

private theorem d1_to_p (w : Nat) :
    BB6.Agent3.CReach (14980+15168*w) (599+608*w) →
    BB6.Agent3.CReach (7787+7888*w) (4192+4248*w) := by
  intro hr
  have h := (BB6.Agent3.evenodd_four_blank_reach_iff
    (14980+15168*w) (599+608*w)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have hx : ((14980+15168*w)+(599+608*w)-5)/2=7787+7888*w :=
    div_two_eq ((14980+15168*w)+(599+608*w)-5)
      (7787+7888*w) (by omega)
  have hy : ((14980+15168*w)+3*(599+608*w)-9)/4=4192+4248*w :=
    div_four_eq ((14980+15168*w)+3*(599+608*w)-9)
      (4192+4248*w) (by omega)
  simpa only [hx,hy] using h

private theorem p_to_q (w : Nat) :
    BB6.Agent3.CReach (7787+7888*w) (4192+4248*w) →
    BB6.Agent3.CReach (11977+12136*w) (2095+2124*w) := by
  intro hr
  have h := six_parent_reach
    (7787+7888*w) (4192+4248*w)
    (by omega) (by omega) (by omega) (by omega) hr
  have hx : (7787+7888*w)+(4192+4248*w)-2=11977+12136*w := by omega
  have hy : ((4192+4248*w)-2)/2=2095+2124*w :=
    div_two_eq ((4192+4248*w)-2) (2095+2124*w) (by omega)
  simpa only [hx,hy] using h

private theorem q_to_r (w : Nat) (hw16 : w%16=5) :
    BB6.Agent3.CReach (11977+12136*w) (2095+2124*w) →
    BB6.Agent3.CReach (7034+7130*w) (4563+4627*w) := by
  intro hr
  have h := (BB6.Agent3.oddodd_lowval_blank_reach_iff
    (11977+12136*w) (2095+2124*w)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)).mp hr
  have hx : ((11977+12136*w)+(2095+2124*w)-4)/2=7034+7130*w :=
    div_two_eq ((11977+12136*w)+(2095+2124*w)-4)
      (7034+7130*w) (by omega)
  have hy : ((11977+12136*w)+3*(2095+2124*w)-10)/4=4563+4627*w :=
    div_four_eq ((11977+12136*w)+3*(2095+2124*w)-10)
      (4563+4627*w) (by omega)
  simpa only [hx,hy] using h

private theorem r_to_r1 (q : Nat) :
    BB6.Agent3.CReach (7034+7130*(16*q+5)) (4563+4627*(16*q+5)) →
    BB6.Agent3.CReach (70380+188112*q) (13848+37016*q) := by
  intro hr
  have h := six_parent_reach
    (7034+7130*(16*q+5)) (4563+4627*(16*q+5))
    (by omega) (by omega) (by omega) (by omega) hr
  have hx :
      (7034+7130*(16*q+5))+(4563+4627*(16*q+5))-2 =
        70380+188112*q := by omega
  have hy :
      ((4563+4627*(16*q+5))-2)/2=13848+37016*q :=
    div_two_eq ((4563+4627*(16*q+5))-2) (13848+37016*q) (r_to_r1_y q)
  simpa only [hx,hy] using h

private theorem r1_to_r2 (q : Nat) :
    BB6.Agent3.CReach (70380+188112*q) (13848+37016*q) →
    BB6.Agent3.CReach (84226+225128*q) (6923+18508*q) := by
  intro hr
  have h := six_parent_reach
    (70380+188112*q) (13848+37016*q)
    (by omega) (by omega) (by omega) (by omega) hr
  have hx :
      (70380+188112*q)+(13848+37016*q)-2 =
        84226+225128*q := by omega
  have hy :
      ((13848+37016*q)-2)/2=6923+18508*q :=
    div_two_eq ((13848+37016*q)-2) (6923+18508*q) (by omega)
  simpa only [hx,hy] using h

private theorem e0_to_e1 (w : Nat) :
    BB6.Agent3.CReach (3444+3488*w) (6366+6448*w) →
    BB6.Agent3.CReach (9808+9936*w) (3182+3224*w) := by
  intro hr
  have h := six_parent_reach
    (3444+3488*w) (6366+6448*w)
    (by omega) (by omega) (by omega) (by omega) hr
  have hx : (3444+3488*w)+(6366+6448*w)-2=9808+9936*w := by omega
  have hy : ((6366+6448*w)-2)/2=3182+3224*w :=
    div_two_eq ((6366+6448*w)-2) (3182+3224*w) (by omega)
  simpa only [hx,hy] using h

private theorem e1_to_e2 (w : Nat) :
    BB6.Agent3.CReach (9808+9936*w) (3182+3224*w) →
    BB6.Agent3.CReach (12988+13160*w) (1590+1612*w) := by
  intro hr
  have h := six_parent_reach
    (9808+9936*w) (3182+3224*w)
    (by omega) (by omega) (by omega) (by omega) hr
  have hx : (9808+9936*w)+(3182+3224*w)-2=12988+13160*w := by omega
  have hy : ((3182+3224*w)-2)/2=1590+1612*w :=
    div_two_eq ((3182+3224*w)-2) (1590+1612*w) (by omega)
  simpa only [hx,hy] using h

private theorem e2_to_e3 (w : Nat) (hw16 : w%16=5) :
    BB6.Agent3.CReach (12988+13160*w) (1590+1612*w) →
    BB6.Agent3.CReach (14576+14772*w) (794+806*w) := by
  intro hr
  have h := six_parent_reach
    (12988+13160*w) (1590+1612*w)
    (by omega) (by omega) (by omega) (by omega) hr
  have hx : (12988+13160*w)+(1590+1612*w)-2=14576+14772*w := by omega
  have hy : ((1590+1612*w)-2)/2=794+806*w :=
    div_two_eq ((1590+1612*w)-2) (794+806*w) (by omega)
  simpa only [hx,hy] using h

private theorem e3_to_e4 (w : Nat) (hw16 : w%16=5) :
    BB6.Agent3.CReach (14576+14772*w) (794+806*w) →
    BB6.Agent3.CReach (15368+15578*w) (396+403*w) := by
  intro hr
  have h := six_parent_reach
    (14576+14772*w) (794+806*w)
    (by omega) (by omega) (by omega) (by omega) hr
  have hx : (14576+14772*w)+(794+806*w)-2=15368+15578*w := by omega
  have hy : ((794+806*w)-2)/2=396+403*w :=
    div_two_eq ((794+806*w)-2) (396+403*w) (by omega)
  simpa only [hx,hy] using h

theorem blank_no_R_s31_w5 (q : Nat) :
    ¬ BB6.Agent3.CReach
      (7034+7130*(16*q+5)) (4563+4627*(16*q+5)) := by
  intro hr
  have hR1 := r_to_r1 q hr
  have hR2 := r1_to_r2 q hR1
  exact (BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    (84226+225128*q) (6923+18508*q)
    (by omega) (by omega) (by omega) (by omega)) hR2

theorem blank_no_E_s31_w5 (q : Nat) :
    ¬ BB6.Agent3.CReach
      (3444+3488*(16*q+5)) (6366+6448*(16*q+5)) := by
  let w := 16*q+5
  have hw16 : w%16=5 := by dsimp [w]; omega
  have hw2 : w%2=1 := by dsimp [w]; omega
  have hw4 : w%4=1 := by dsimp [w]; omega
  intro hr
  have hE1 := e0_to_e1 w hr
  have hE2 := e1_to_e2 w hE1
  have hE3 := e2_to_e3 w hw16 hE2
  have hE4 := e3_to_e4 w hw16 hE3
  exact (BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    (15368+15578*w) (396+403*w)
    (by omega) (by omega) (by omega) (by omega)) hE4

/-- The L_s parent for s=32*w+31 is excluded on w=16*q+5.
    Its direct parent is normalized through the odd/odd low-valuation edge
    and two further six-even-right edges to an odd-right sum-one state.
    Its bounce parent is excluded by four six-even-right edges. -/
theorem blank_no_L_s31_w5 (q : Nat) :
    ¬ BB6.Agent3.CReach
      (11382+11520*(16*q+5)) (2402+2432*(16*q+5)) := by
  let w := 16*q+5
  let x := 11382+11520*w
  let y := 2402+2432*w
  let S := 1723+1744*w
  have hD : ¬ BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
    intro hr
    have hx : x+y-2=13782+13952*w := by dsimp [x,y]; omega
    have hy : (y-2)/2=1200+1216*w :=
      div_two_eq (y-2) (1200+1216*w) (by dsimp [y]; omega)
    have hD0 : BB6.Agent3.CReach
        (13782+13952*w) (1200+1216*w) := by
      simpa only [hx,hy] using hr
    have hD1 := d0_to_d1 w hD0
    have hP := d1_to_p w hD1
    have hQ := p_to_q w hP
    have hR : BB6.Agent3.CReach
        (7034+7130*w) (4563+4627*w) := by
      exact q_to_r w (by dsimp [w]; omega) hQ
    have hR' : BB6.Agent3.CReach
        (7034+7130*(16*q+5)) (4563+4627*(16*q+5)) := by
      simpa only [w] using hR
    exact (blank_no_R_s31_w5 q) hR'
  have hE : ¬ BB6.Agent3.CReach
      (2*S-2) ((x+2*y-2*S-8)/2) := by
    intro hr
    have hE0 : BB6.Agent3.CReach
        (3444+3488*w) (6366+6448*w) := by
      have hx : 2*S-2=3444+3488*w := by dsimp [S]; omega
      have hy : (x+2*y-2*S-8)/2=6366+6448*w :=
        div_two_eq (x+2*y-2*S-8) (6366+6448*w) (by dsimp [x,y,S]; omega)
      simpa only [hx,hy] using hr
    have hE0' : BB6.Agent3.CReach
        (3444+3488*(16*q+5)) (6366+6448*(16*q+5)) := by
      simpa only [w] using hE0
    exact (blank_no_E_s31_w5 q) hE0'
  change ¬ BB6.Agent3.CReach x y
  exact BB6.Agent11M0SumZeroVerified.blank_no_sumzero_target
    x y S (by dsimp [x]; omega) (by dsimp [x]; omega)
    (by dsimp [y]; omega) (by dsimp [y]; omega)
    (by dsimp [x,y,S]; omega) (by dsimp [S]; omega)
    (by dsimp [S]; omega) hD hE

/-- A_s for s=32*w+31 is excluded when w=16*q+5, using the
    preceding L_s result and the existing B_s exclusion. -/
theorem blank_no_A_s31_w5 (q : Nat) :
    ¬ BB6.Agent3.CReach (39858+106496*q) (29126+77824*q) := by
  let w := 16*q+5
  let x := 39858+106496*q
  let y := 29126+77824*q
  let S := 8623+23040*q
  have hD : ¬ BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
    have hL := blank_no_L_s31_w5 q
    have hx : x+y-2=11382+11520*w := by dsimp [x,y,w]; omega
    have hy : (y-2)/2=2402+2432*w := by
      apply div_two_eq
      dsimp [y,w]
      omega
    rw [hx,hy]
    exact hL
  have hE : ¬ BB6.Agent3.CReach
      (2*S-2) ((x+2*y-2*S-8)/2) := by
    have hB := BB6.Agent11M0SumZeroS31.blank_no_B_s31 w
    have hx : 2*S-2=2844+2880*w := by dsimp [S,w]; omega
    have hy : (x+2*y-2*S-8)/2=6668+6752*w := by
      apply div_two_eq
      dsimp [x,y,S,w]
      omega
    rw [hx,hy]
    exact hB
  have hA := BB6.Agent11M0SumZeroVerified.blank_no_sumzero_target
    x y S (by dsimp [x]; omega) (by dsimp [x]; omega)
    (by dsimp [y]; omega) (by dsimp [y]; omega)
    (by dsimp [x,y,S]; omega) (by dsimp [S]; omega)
    (by dsimp [S]; omega) hD hE
  change ¬ BB6.Agent3.CReach x y
  exact hA

/-- New m=0 high-stop cylinder: t=383 mod 1024, equivalently
    j=12263 mod 32768. This residue is disjoint from the four
    previously reported m=0 high-stop classes. -/
theorem high_stop_mzero_s31_w5 (j k : Nat)
    (hj : j%32768=12263)
    (hstop : k+j+5=4*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  let q := (j-12263)/32768
  have hjform : j=12263+32768*q := by dsimp [q]; omega
  have hkform : k=36796+98304*q := by rw [hjform] at hstop; omega
  have hxform : 2*j+3=24529+65536*q := by rw [hjform]; omega
  intro hr
  have hr' : BB6.Agent3.CReach
      (24529+65536*q) (36796+98304*q) := by
    simpa only [hxform,hkform] using hr
  have hstart : BB6.Agent3.CReach
      (17+64*(1024*q+383)) (28+96*(1024*q+383)) := by
    have hx : 17+64*(1024*q+383)=24529+65536*q := by omega
    have hy : 28+96*(1024*q+383)=36796+98304*q := root_start_y q
    simpa only [hx,hy] using hr'
  have hA := BB6.Agent11M0SumZeroVerified.mzero_first_two_reach
    (1024*q+383) hstart
  have hA' : BB6.Agent3.CReach
      (39858+106496*q) (29126+77824*q) := by
    have hx : 26+104*(1024*q+383)=39858+106496*q := by omega
    have hy : 18+76*(1024*q+383)=29126+77824*q := root_final_y q
    simpa only [hx,hy] using hA
  exact blank_no_A_s31_w5 q hA'

#print axioms blank_no_R_s31_w5
#print axioms blank_no_E_s31_w5
#print axioms blank_no_L_s31_w5
#print axioms blank_no_A_s31_w5
#print axioms high_stop_mzero_s31_w5
end BB6.Agent11M0SumZeroS31W5
