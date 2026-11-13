import M0EvenEvenSumZeroS31W1
import M0EvenEvenSumZeroS31W13Q275
import OddOddLowVal
import OddSevenSliver
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0SumZeroS31W13Q403

private theorem six_parent_reach (x y : Nat)
    (hy : 6≤y) (he : y%2=0)
    (h0 : (x+y)%8≠0) (h7 : (x+y)%8≠7)
    (hr : BB6.Agent3.CReach x y) :
    BB6.Agent3.CReach (x+y-2) ((y-2)/2) :=
  (BB6.Agent46.six_even_right_blank_reach_iff x y hy he h0 h7).mp hr

/-- The second S31 w=1 mod 4 residual cylinder, with q=2048*e+403.
    The direct parent is followed through odd/odd low-valuation and two
    six-even-right inverses; the depth-one bounce parent is excluded after
    one six-even-right inverse. -/
theorem blank_no_L_s31_w13_q403 (e : Nat) :
    ¬ BB6.Agent3.CReach
      (11382+11520*(32768*e+6461))
      (2402+2432*(32768*e+6461)) := by
  let q := 2048*e+403
  let w := 16*q+13
  have hw : w=32768*e+6461 := by dsimp [w,q]; omega
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
  have hR1e : BB6.Agent3.CReach
      (75973572+385253376*e) (14949804+75808768*e) := by
    have hx : 164436+188112*q=75973572+385253376*e := by
      dsimp [q]; omega
    have hy : 32356+37016*q=14949804+75808768*e := by
      dsimp [q]; omega
    simpa only [hx,hy] using hR1q
  let x := 75973572+385253376*e
  let y := 14949804+75808768*e
  let S := 11365422+57632768*e
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent3.cReach_parent_of_left_gt5 x y (by dsimp [x]; omega) hR1e
  have hparents := BB6.Agent11M0SumZeroVerified.even_even_sumzero_parent
    a k x y S
    (by dsimp [x]; omega) (by dsimp [x]; omega)
    (by dsimp [y]; omega) (by dsimp [y]; omega)
    (by dsimp [x,y,S]; omega)
    (by dsimp [S]; omega) (by dsimp [S]; omega) hstep
  rcases hparents with hD | hE
  · rcases hD with ⟨ha,hk⟩
    have hD0 : BB6.Agent3.CReach
        (90923374+461062144*e) (7474901+37904384*e) := by
      have hx : x+y-2=90923374+461062144*e := by
        dsimp [x,y]; omega
      have hy : (y-2)/2=7474901+37904384*e := by
        dsimp [y]; omega
      rw [ha,hk] at hprev
      simpa only [hx,hy] using hprev
    have hP := (BB6.Agent3.evenodd_four_blank_reach_iff
      (90923374+461062144*e) (7474901+37904384*e)
      (by omega) (by omega) (by omega) (by omega)).mp hD0
    have hP' : BB6.Agent3.CReach
        (49199135+249483264*e) (28337017+143693824*e) := by
      have hx : ((90923374+461062144*e)+(7474901+37904384*e)-5)/2 =
          49199135+249483264*e := by omega
      have hy : ((90923374+461062144*e)+3*(7474901+37904384*e)-9)/4 =
          28337017+143693824*e := by omega
      simpa only [hx,hy] using hP
    have hQ := (BB6.Agent3.oddodd_val3_blank_reach_iff
      (49199135+249483264*e) (28337017+143693824*e)
      (by omega) (by omega) (by omega) (by omega) (by omega)).mp hP'
    have hQ' : BB6.Agent3.CReach
        (38768074+196588544*e) (33552544+170141184*e) := by
      have hx : ((49199135+249483264*e)+(28337017+143693824*e)-4)/2 =
          38768074+196588544*e := by omega
      have hy : ((49199135+249483264*e)+3*(28337017+143693824*e)-10)/4 =
          33552544+170141184*e := by omega
      simpa only [hx,hy] using hQ
    have hQ1 := six_parent_reach
      (38768074+196588544*e) (33552544+170141184*e)
      (by omega) (by omega) (by omega) (by omega) hQ'
    have hQ1' : BB6.Agent3.CReach
        (72320616+366729728*e) (16776271+85070592*e) := by
      have hx : (38768074+196588544*e)+(33552544+170141184*e)-2 =
          72320616+366729728*e := by omega
      have hy : ((33552544+170141184*e)-2)/2 =
          16776271+85070592*e := by omega
      simpa only [hx,hy] using hQ1
    obtain ⟨a7,k7,hprev7,hstep7⟩ :=
      BB6.Agent3.cReach_parent_of_left_gt5
        (72320616+366729728*e) (16776271+85070592*e)
        (by omega) hQ1'
    have h7eq := (BB6.Agent3.odd_seven_parent_iff
      a7 k7 (72320616+366729728*e) (16776271+85070592*e)
      (by omega) (by omega) (by omega) (by omega) (by omega)).mp hstep7
    have ha7 : a7=44548441+225900160*e := by
      rcases h7eq with ⟨hsum,hcost⟩
      omega
    have hk7 : k7=30662355+155485376*e := by
      rcases h7eq with ⟨hsum,hcost⟩
      omega
    have hA' : BB6.Agent3.CReach
        (44548441+225900160*e) (30662355+155485376*e) := by
      simpa only [ha7,hk7] using hprev7
    have hB := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (44548441+225900160*e) (30662355+155485376*e)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp hA'
    have hB' : BB6.Agent3.CReach
        (37605396+190692768*e) (34133874+173089072*e) := by
      have hx : ((44548441+225900160*e)+(30662355+155485376*e)-4)/2 =
          37605396+190692768*e := by omega
      have hy : ((44548441+225900160*e)+3*(30662355+155485376*e)-10)/4 =
          34133874+173089072*e := by omega
      simpa only [hx,hy] using hB
    have hC := six_parent_reach
      (37605396+190692768*e) (34133874+173089072*e)
      (by omega) (by omega) (by omega) (by omega) hB'
    have hC' : BB6.Agent3.CReach
        (71739268+363781840*e) (17066936+86544536*e) := by
      have hx : (37605396+190692768*e)+(34133874+173089072*e)-2 =
          71739268+363781840*e := by omega
      have hy : ((34133874+173089072*e)-2)/2 =
          17066936+86544536*e := by omega
      simpa only [hx,hy] using hC
    have hD2 := six_parent_reach
      (71739268+363781840*e) (17066936+86544536*e)
      (by omega) (by omega) (by omega) (by omega) hC'
    have hD2' : BB6.Agent3.CReach
        (88806202+450326376*e) (8533467+43272268*e) := by
      have hx : (71739268+363781840*e)+(17066936+86544536*e)-2 =
          88806202+450326376*e := by omega
      have hy : ((17066936+86544536*e)-2)/2 =
          8533467+43272268*e := by omega
      simpa only [hx,hy] using hD2
    exact (BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (88806202+450326376*e) (8533467+43272268*e)
      (by omega) (by omega) (by omega) (by omega)) hD2'
  · rcases hE with ⟨ha,hk⟩
    have hE0 : BB6.Agent3.CReach
        (22730842+115265536*e) (41571164+75808768*e) := by
      have hx : 2*S-2=22730842+115265536*e := by dsimp [S]; omega
      have hy : (x+2*y-2*S-8)/2=41571164+75808768*e := by
        dsimp [x,y,S]; omega
      rw [ha,hk] at hprev
      simpa only [hx,hy] using hprev
    have hE1 := six_parent_reach
      (22730842+115265536*e) (41571164+75808768*e)
      (by omega) (by omega) (by omega) (by omega) hE0
    have hE1' : BB6.Agent3.CReach
        (64302004+191074304*e) (20785581+37904384*e) := by
      have hx : (22730842+115265536*e)+(41571164+75808768*e)-2 =
          64302004+191074304*e := by omega
      have hy : ((41571164+75808768*e)-2)/2 =
          20785581+37904384*e := by omega
      simpa only [hx,hy] using hE1
    exact (BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (64302004+191074304*e) (20785581+37904384*e)
      (by omega) (by omega) (by omega) (by omega)) hE1'

#print axioms blank_no_L_s31_w13_q403

/-- A second nested m=0 high-stop exclusion on the s=32*w+31 ray. -/
theorem high_stop_mzero_s31_w13_q403 (j k : Nat)
    (hj : j%67108864=13234151)
    (hstop : k+j+5=4*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  let e := (j-13234151)/67108864
  have hjform : j=13234151+67108864*e := by dsimp [e]; omega
  have hkform : k=39702460+201326592*e := by
    rw [hjform] at hstop
    dsimp [e]
    omega
  let s := 1048576*e+206783
  let w := 32768*e+6461
  let t := 2097152*e+413567
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
    exact blank_no_L_s31_w13_q403 e
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

#print axioms high_stop_mzero_s31_w13_q403

/-- Unified two-cylinder statement: with q=128*g+19, the direct L-parent
    closes when g=2 mod 4 or g=3 mod 16. -/
theorem high_stop_mzero_s31_w13_q128g19 (g j k : Nat)
    (hg : g%4=2 ∨ g%16=3)
    (hj : j=651239+4194304*g)
    (hstop : k+j+5=4*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  rcases hg with hg2 | hg3
  · let d := (g-2)/4
    have hgform : g=4*d+2 := by dsimp [d]; omega
    have hjform : j=9039847+16777216*d := by
      rw [hj,hgform]
      dsimp [d]
      omega
    have hjmod : j%16777216=9039847 := by rw [hjform]; omega
    exact BB6.Agent11M0SumZeroS31W13Q275.high_stop_mzero_s31_w13_q275
      j k hjmod hstop
  · let e := (g-3)/16
    have heform : g=16*e+3 := by dsimp [e]; omega
    have hjform : j=13234151+67108864*e := by
      rw [hj,heform]
      dsimp [e]
      omega
    have hjmod : j%67108864=13234151 := by rw [hjform]; omega
    exact high_stop_mzero_s31_w13_q403 j k hjmod hstop

#print axioms high_stop_mzero_s31_w13_q128g19
end BB6.Agent11M0SumZeroS31W13Q403
