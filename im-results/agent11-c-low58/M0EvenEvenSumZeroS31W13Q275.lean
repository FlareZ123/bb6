import M0EvenEvenSumZeroS31W1
import OddSevenSliver
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0SumZeroS31W13Q275

private theorem six_parent_reach (x y : Nat)
    (hy : 6≤y) (he : y%2=0)
    (h0 : (x+y)%8≠0) (h7 : (x+y)%8≠7)
    (hr : BB6.Agent3.CReach x y) :
    BB6.Agent3.CReach (x+y-2) ((y-2)/2) :=
  (BB6.Agent46.six_even_right_blank_reach_iff x y hy he h0 h7).mp hr

/-- The L_s parent is excluded on the nested cylinder
    w = 8192*d+4413 (equivalently q=512*d+275 in w=16*q+13).
    The proof follows the direct parent through even/odd-four,
    odd/odd-val-three, six-even-right, odd-seven, and odd/odd-val-three
    source inverses. The competing depth-one bounce parent is excluded
    after one six-even-right inverse. -/
theorem blank_no_L_s31_w13_q275 (d : Nat) :
    ¬ BB6.Agent3.CReach
      (11382+11520*(8192*d+4413))
      (2402+2432*(8192*d+4413)) := by
  let q := 512*d+275
  let w := 16*q+13
  have hw : w=8192*d+4413 := by dsimp [w,q]; omega
  intro hL
  have hLw : BB6.Agent3.CReach (11382+11520*w) (2402+2432*w) := by
    simpa [hw] using hL
  have hLz : BB6.Agent3.CReach
      (11382+11520*(4*(4*q+3)+1))
      (2402+2432*(4*(4*q+3)+1)) := by
    have hx : 11382+11520*(4*(4*q+3)+1)=11382+11520*w := by
      dsimp [w]; omega
    have hy : 2402+2432*(4*(4*q+3)+1)=2402+2432*w := by
      dsimp [w]; omega
    simpa only [hx,hy] using hLw
  have hR := BB6.Agent11M0SumZeroS31W1.l_s31_w1mod4_parent_reduction
    (4*q+3) hLz
  have hR' : BB6.Agent3.CReach
      (99724+114080*q) (64714+74032*q) := by
    have hx : 7034+7130*(4*(4*q+3)+1)=99724+114080*q := by omega
    have hy : 4563+4627*(4*(4*q+3)+1)=64714+74032*q := by omega
    simpa only [hx,hy] using hR
  have hR1 := six_parent_reach
    (99724+114080*q) (64714+74032*q)
    (by dsimp [q]; omega) (by dsimp [q]; omega)
    (by dsimp [q]; omega) (by dsimp [q]; omega) hR'
  have hR1q : BB6.Agent3.CReach
      (164436+188112*q) (32356+37016*q) := by
    have hx : (99724+114080*q)+(64714+74032*q)-2 =
        164436+188112*q := by omega
    have hy : ((64714+74032*q)-2)/2=32356+37016*q := by omega
    simpa only [hx,hy] using hR1
  have hR1d : BB6.Agent3.CReach
      (51895236+96313344*d) (10211756+18952192*d) := by
    have hx : 164436+188112*q=51895236+96313344*d := by
      dsimp [q]; omega
    have hy : 32356+37016*q=10211756+18952192*d := by
      dsimp [q]; omega
    simpa only [hx,hy] using hR1q
  let x := 51895236+96313344*d
  let y := 10211756+18952192*d
  let S := 7763374+14408192*d
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent3.cReach_parent_of_left_gt5 x y (by dsimp [x]; omega) hR1d
  have hparents := BB6.Agent11M0SumZeroVerified.even_even_sumzero_parent
    a k x y S
    (by dsimp [x]; omega) (by dsimp [x]; omega)
    (by dsimp [y]; omega) (by dsimp [y]; omega)
    (by dsimp [x,y,S]; omega)
    (by dsimp [S]; omega) (by dsimp [S]; omega) hstep
  rcases hparents with hD | hE
  · rcases hD with ⟨ha,hk⟩
    have hD0 : BB6.Agent3.CReach
        (62106990+115265536*d) (5105877+9476096*d) := by
      have hx : x+y-2=62106990+115265536*d := by
        dsimp [x,y]; omega
      have hy : (y-2)/2=5105877+9476096*d := by
        dsimp [y]; omega
      rw [ha,hk] at hprev
      simpa only [hx,hy] using hprev
    have hP := (BB6.Agent3.evenodd_four_blank_reach_iff
      (62106990+115265536*d) (5105877+9476096*d)
      (by omega) (by omega) (by omega) (by omega)).mp hD0
    have hP' : BB6.Agent3.CReach
        (33606431+62370816*d) (19356153+35923456*d) := by
      have hx : ((62106990+115265536*d)+(5105877+9476096*d)-5)/2 =
          33606431+62370816*d := by omega
      have hy : ((62106990+115265536*d)+3*(5105877+9476096*d)-9)/4 =
          19356153+35923456*d := by omega
      simpa only [hx,hy] using hP
    have hQ := (BB6.Agent3.oddodd_val3_blank_reach_iff
      (33606431+62370816*d) (19356153+35923456*d)
      (by omega) (by omega) (by omega) (by omega) (by omega)).mp hP'
    have hQ' : BB6.Agent3.CReach
        (26481290+49147136*d) (22918720+42535296*d) := by
      have hx : ((33606431+62370816*d)+(19356153+35923456*d)-4)/2 =
          26481290+49147136*d := by omega
      have hy : ((33606431+62370816*d)+3*(19356153+35923456*d)-10)/4 =
          22918720+42535296*d := by omega
      simpa only [hx,hy] using hQ
    have hQ1 := six_parent_reach
      (26481290+49147136*d) (22918720+42535296*d)
      (by omega) (by omega) (by omega) (by omega) hQ'
    have hQ1' : BB6.Agent3.CReach
        (49400008+91682432*d) (11459359+21267648*d) := by
      have hx : (26481290+49147136*d)+(22918720+42535296*d)-2 =
          49400008+91682432*d := by omega
      have hy : ((22918720+42535296*d)-2)/2 =
          11459359+21267648*d := by omega
      simpa only [hx,hy] using hQ1
    have hA := (BB6.Agent3.odd_seven_parent_iff
      (49400008+91682432*d) (11459359+21267648*d)
      (by omega) (by omega) (by omega) (by omega) (by omega)).mp hQ1'
    have hA' : BB6.Agent3.CReach
        (30429681+56475040*d) (20944519+38871344*d) := by
      have hx : ((49400008+91682432*d)+(11459359+21267648*d)-5)/2 =
          30429681+56475040*d := by omega
      have hy : ((49400008+91682432*d)+3*(11459359+21267648*d)-9)/4 =
          20944519+38871344*d := by omega
      simpa only [hx,hy] using hA
    have hB := (BB6.Agent3.oddodd_val3_blank_reach_iff
      (30429681+56475040*d) (20944519+38871344*d)
      (by omega) (by omega) (by omega) (by omega) (by omega)).mp hA'
    have hB' : BB6.Agent3.CReach
        (25687098+47673192*d) (23315807+43272268*d) := by
      have hx : ((30429681+56475040*d)+(20944519+38871344*d)-4)/2 =
          25687098+47673192*d := by omega
      have hy : ((30429681+56475040*d)+3*(20944519+38871344*d)-10)/4 =
          23315807+43272268*d := by omega
      simpa only [hx,hy] using hB
    exact (BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (25687098+47673192*d) (23315807+43272268*d)
      (by omega) (by omega) (by omega) (by omega)) hB'
  · rcases hE with ⟨ha,hk⟩
    have hE0 : BB6.Agent3.CReach
        (15526746+28816384*d) (28395996+52700672*d) := by
      have hx : 2*S-2=15526746+28816384*d := by dsimp [S]; omega
      have hy : (x+2*y-2*S-8)/2=28395996+52700672*d := by
        dsimp [x,y,S]; omega
      rw [ha,hk] at hprev
      simpa only [hx,hy] using hprev
    have hE1 := six_parent_reach
      (15526746+28816384*d) (28395996+52700672*d)
      (by omega) (by omega) (by omega) (by omega) hE0
    have hE1' : BB6.Agent3.CReach
        (43922740+81517056*d) (14197997+26350336*d) := by
      have hx : (15526746+28816384*d)+(28395996+52700672*d)-2 =
          43922740+81517056*d := by omega
      have hy : ((28395996+52700672*d)-2)/2 =
          14197997+26350336*d := by omega
      simpa only [hx,hy] using hE1
    exact (BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (43922740+81517056*d) (14197997+26350336*d)
      (by omega) (by omega) (by omega) (by omega)) hE1'

#print axioms blank_no_L_s31_w13_q275

/-- A second nested infinite m=0 high-stop exclusion. The new parameter
    is t=524288*d+282495, equivalently j=9039847+16777216*d.
    It is disjoint from the five earlier certified m=0 cylinders. -/
theorem high_stop_mzero_s31_w13_q275 (j k : Nat)
    (hj : j%16777216=9039847)
    (hstop : k+j+5=4*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  let d := (j-9039847)/16777216
  have hjform : j=9039847+16777216*d := by dsimp [d]; omega
  have hkform : k=27119548+50331648*d := by
    rw [hjform] at hstop
    dsimp [d]
    omega
  let s := 262144*d+141247
  let w := 8192*d+4413
  let t := 524288*d+282495
  have hsform : s=32*w+31 := by dsimp [s,w]; omega
  have htform : t=2*s+1 := by dsimp [s,t]; omega
  intro hr
  have hstart : BB6.Agent3.CReach (17+64*t) (28+96*t) := by
    have hx : 2*j+3=17+64*t := by rw [hjform]; dsimp [t]; omega
    have hy : k=28+96*t := by rw [hkform]; dsimp [t]; omega
    simpa only [hx,hy] using hr
  have hA := BB6.Agent11M0SumZeroVerified.mzero_first_two_reach t hstart
  have hA' : BB6.Agent3.CReach (130+208*s) (94+152*s) := by
    have hx : 26+104*t=130+208*s := by dsimp [s,t]; omega
    have hy : 18+76*t=94+152*s := by dsimp [s,t]; omega
    simpa only [hx,hy] using hA
  have hD : ¬ BB6.Agent3.CReach
      ((130+208*s)+(94+152*s)-2) ((94+152*s-2)/2) := by
    have hx : (130+208*s)+(94+152*s)-2=11382+11520*w := by
      dsimp [s,w]; omega
    have hy : (94+152*s-2)/2=2402+2432*w := by
      dsimp [s,w]; omega
    rw [hx,hy]
    exact blank_no_L_s31_w13_q275 d
  have hE : ¬ BB6.Agent3.CReach
      (2*(28+45*s)-2)
      ((130+208*s+2*(94+152*s)-2*(28+45*s)-8)/2) := by
    have hx : 2*(28+45*s)-2=2844+2880*w := by
      dsimp [s,w]; omega
    have hy :
        (130+208*s+2*(94+152*s)-2*(28+45*s)-8)/2=6668+6752*w := by
      dsimp [s,w]; omega
    rw [hx,hy]
    exact BB6.Agent11M0SumZeroS31.blank_no_B_s31 w
  have hAfalse := BB6.Agent11M0SumZeroVerified.blank_no_sumzero_target
    (130+208*s) (94+152*s) (28+45*s)
    (by dsimp [s]; omega) (by dsimp [s]; omega)
    (by dsimp [s]; omega) (by dsimp [s]; omega)
    (by dsimp [s]; omega) (by dsimp [s]; omega)
    (by dsimp [s]; omega) hD hE
  exact hAfalse hA'

#print axioms high_stop_mzero_s31_w13_q275
end BB6.Agent11M0SumZeroS31W13Q275
