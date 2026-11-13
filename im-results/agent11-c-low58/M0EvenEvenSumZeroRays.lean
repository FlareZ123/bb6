import M0EvenEvenSumZeroParents
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0SumZero
open BB6.Agent46

private theorem blank_no_odd_image (x y : Nat)
    (hy5 : 5≤y) (hyOdd : y%2=1) (hs : (x+y)%4=1) :
    ¬ BB6.Agent3.CReach x y := by
  intro hreach
  rcases hreach with ⟨time, hrun⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hrun
      omega
  | succ n =>
      have hbad :=
        BB6.Agent3.blank_section_odd_image n x y hrun hy5 hyOdd
      omega

/-- The first two original-section inverse edges on the high m=0 ray.
    Unlike the four-edge lemma, these two edges need no t%4 hypothesis. -/
theorem mzero_first_two_reach (t : Nat)
    (hr : BB6.Agent3.CReach (17+64*t) (28+96*t)) :
    BB6.Agent3.CReach (26+104*t) (18+76*t) := by
  have hp1 := (six_even_right_blank_reach_iff
    (17+64*t) (28+96*t)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have h1 : BB6.Agent3.CReach (43+160*t) (13+48*t) := by
    have hx : (17+64*t)+(28+96*t)-2=43+160*t := by omega
    have hy : ((28+96*t)-2)/2=13+48*t := by omega
    simpa only [hx,hy] using hp1
  have hp2 := (BB6.Agent3.oddodd_val3_blank_reach_iff
    (43+160*t) (13+48*t)
    (by omega) (by omega) (by omega) (by omega) (by omega)).mp h1
  have h2 : BB6.Agent3.CReach (26+104*t) (18+76*t) := by
    have hx : ((43+160*t)+(13+48*t)-4)/2=26+104*t := by omega
    have hy : ((43+160*t)+3*(13+48*t)-10)/4=18+76*t := by omega
    change (∃ n, BB6.Agent8Section.run secNext n (some (5,1)) =
      some (26+104*t,18+76*t))
    simpa only [hx,hy] using hp2
  exact h2

/-- The bounce-parent branch B_(0,s) for s=32v+29 is eliminated by
    three source-certified six-of-eight direct-parent reductions. -/
private theorem blank_no_mzero_B_1895 (v : Nat) :
    ¬ BB6.Agent3.CReach (2664+2880*v) (6246+6752*v) := by
  intro hr
  have hp1 := (six_even_right_blank_reach_iff
    (2664+2880*v) (6246+6752*v)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have h1 : BB6.Agent3.CReach (8908+9632*v) (3122+3376*v) := by
    have hx : (2664+2880*v)+(6246+6752*v)-2=8908+9632*v := by omega
    have hy : ((6246+6752*v)-2)/2=3122+3376*v := by omega
    simpa only [hx,hy] using hp1
  have hp2 := (six_even_right_blank_reach_iff
    (8908+9632*v) (3122+3376*v)
    (by omega) (by omega) (by omega) (by omega)).mp h1
  have h2 : BB6.Agent3.CReach (12028+13008*v) (1560+1688*v) := by
    have hx : (8908+9632*v)+(3122+3376*v)-2=12028+13008*v := by omega
    have hy : ((3122+3376*v)-2)/2=1560+1688*v := by omega
    simpa only [hx,hy] using hp2
  have hp3 := (six_even_right_blank_reach_iff
    (12028+13008*v) (1560+1688*v)
    (by omega) (by omega) (by omega) (by omega)).mp h2
  have h3 : BB6.Agent3.CReach (13586+14696*v) (779+844*v) := by
    have hx : (12028+13008*v)+(1560+1688*v)-2=13586+14696*v := by omega
    have hy : ((1560+1688*v)-2)/2=779+844*v := by omega
    simpa only [hx,hy] using hp3
  exact blank_no_odd_image (13586+14696*v) (779+844*v)
    (by omega) (by omega) (by omega) h3

/-- The direct-parent branch L_s for s=32v+29 has exactly two
    possible parents. Its direct parent is forced into the odd-image
    forbidden wedge; its depth-one bounce parent is already there. -/
private theorem blank_no_mzero_L_1895 (v : Nat) :
    ¬ BB6.Agent3.CReach (10662+11520*v) (2250+2432*v) := by
  intro hL
  have hp := eveneven_sumzero_blank_reach_parent
    (10662+11520*v) (2250+2432*v) (1614+1744*v)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hL
  rcases hp with hD | hE
  · have hpD := (six_even_right_blank_reach_iff
      (12910+13952*v) (1124+1216*v)
      (by omega) (by omega) (by omega) (by omega)).mp hD
    have hD' : BB6.Agent3.CReach (14032+15168*v) (561+608*v) := by
      have hx : (12910+13952*v)+(1124+1216*v)-2=14032+15168*v := by omega
      have hy : ((1124+1216*v)-2)/2=561+608*v := by omega
      simpa only [hx,hy] using hpD
    exact blank_no_odd_image (14032+15168*v) (561+608*v)
      (by omega) (by omega) (by omega) hD'
  · exact blank_no_odd_image (3226+3488*v) (5963+6448*v)
      (by omega) (by omega) (by omega) hE

/-- The whole residual A_(32v+29) is blank-unreachable. The
    source-parent disjunction is the only branching step; both branches
    are closed by the existing exact even-right and odd-image lemmas. -/
theorem blank_no_mzero_t59_ray (v : Nat) :
    ¬ BB6.Agent3.CReach (6162+6656*v) (4502+4864*v) := by
  intro hA
  have hA' : BB6.Agent3.CReach
      (130+208*(32*v+29)) (94+152*(32*v+29)) := by
    have hx : 130+208*(32*v+29)=6162+6656*v := by omega
    have hy : 94+152*(32*v+29)=4502+4864*v := by omega
    simpa only [hx,hy] using hA
  rcases mzero_odd_sumzero_reach_parents (32*v+29) (by omega) hA' with hL | hB
  · have hL' : BB6.Agent3.CReach
      (10662+11520*v) (2250+2432*v) := by
        have hx : 222+360*(32*v+29)=10662+11520*v := by omega
        have hy : 46+76*(32*v+29)=2250+2432*v := by omega
        simpa only [hx,hy] using hL
    exact blank_no_mzero_L_1895 v hL'
  · have hB' : BB6.Agent3.CReach
      (2664+2880*v) (6246+6752*v) := by
        have hx : 54+90*(32*v+29)=2664+2880*v := by omega
        have hy : 127+211*(32*v+29)=6246+6752*v := by omega
        simpa only [hx,hy] using hB
    exact blank_no_mzero_B_1895 v hB'

/-- The bounce-parent branch B_(0,s) for s=128w+5 is eliminated by
    five source-certified six-of-eight direct-parent reductions. -/
private theorem blank_no_mzero_B_359 (w : Nat) :
    ¬ BB6.Agent3.CReach (504+11520*w) (1182+27008*w) := by
  intro hr
  have hp1 := (six_even_right_blank_reach_iff
    (504+11520*w) (1182+27008*w)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have h1 : BB6.Agent3.CReach (1684+38528*w) (590+13504*w) := by
    have hx : (504+11520*w)+(1182+27008*w)-2=1684+38528*w := by omega
    have hy : ((1182+27008*w)-2)/2=590+13504*w := by omega
    simpa only [hx,hy] using hp1
  have hp2 := (six_even_right_blank_reach_iff
    (1684+38528*w) (590+13504*w)
    (by omega) (by omega) (by omega) (by omega)).mp h1
  have h2 : BB6.Agent3.CReach (2272+52032*w) (294+6752*w) := by
    have hx : (1684+38528*w)+(590+13504*w)-2=2272+52032*w := by omega
    have hy : ((590+13504*w)-2)/2=294+6752*w := by omega
    simpa only [hx,hy] using hp2
  have hp3 := (six_even_right_blank_reach_iff
    (2272+52032*w) (294+6752*w)
    (by omega) (by omega) (by omega) (by omega)).mp h2
  have h3 : BB6.Agent3.CReach (2564+58784*w) (146+3376*w) := by
    have hx : (2272+52032*w)+(294+6752*w)-2=2564+58784*w := by omega
    have hy : ((294+6752*w)-2)/2=146+3376*w := by omega
    simpa only [hx,hy] using hp3
  have hp4 := (six_even_right_blank_reach_iff
    (2564+58784*w) (146+3376*w)
    (by omega) (by omega) (by omega) (by omega)).mp h3
  have h4 : BB6.Agent3.CReach (2708+62160*w) (72+1688*w) := by
    have hx : (2564+58784*w)+(146+3376*w)-2=2708+62160*w := by omega
    have hy : ((146+3376*w)-2)/2=72+1688*w := by omega
    simpa only [hx,hy] using hp4
  have hp5 := (six_even_right_blank_reach_iff
    (2708+62160*w) (72+1688*w)
    (by omega) (by omega) (by omega) (by omega)).mp h4
  have h5 : BB6.Agent3.CReach (2778+63848*w) (35+844*w) := by
    have hx : (2708+62160*w)+(72+1688*w)-2=2778+63848*w := by omega
    have hy : ((72+1688*w)-2)/2=35+844*w := by omega
    simpa only [hx,hy] using hp5
  exact blank_no_odd_image (2778+63848*w) (35+844*w)
    (by omega) (by omega) (by omega) h5

/-- The direct-parent branch L_s for s=128w+5 has exactly two
    possible parents. Its direct parent is forced into the odd-image
    forbidden wedge; its depth-one bounce parent is already there. -/
private theorem blank_no_mzero_L_359 (w : Nat) :
    ¬ BB6.Agent3.CReach (2022+46080*w) (426+9728*w) := by
  intro hL
  have hp := eveneven_sumzero_blank_reach_parent
    (2022+46080*w) (426+9728*w) (306+6976*w)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hL
  rcases hp with hD | hE
  · have hpD := (six_even_right_blank_reach_iff
      (2446+55808*w) (212+4864*w)
      (by omega) (by omega) (by omega) (by omega)).mp hD
    have hD' : BB6.Agent3.CReach (2656+60672*w) (105+2432*w) := by
      have hx : (2446+55808*w)+(212+4864*w)-2=2656+60672*w := by omega
      have hy : ((212+4864*w)-2)/2=105+2432*w := by omega
      simpa only [hx,hy] using hpD
    exact blank_no_odd_image (2656+60672*w) (105+2432*w)
      (by omega) (by omega) (by omega) hD'
  · exact blank_no_odd_image (610+13952*w) (1127+25792*w)
      (by omega) (by omega) (by omega) hE

/-- The whole residual A_(128w+5) is blank-unreachable. -/
theorem blank_no_mzero_t11_ray (w : Nat) :
    ¬ BB6.Agent3.CReach (1170+26624*w) (854+19456*w) := by
  intro hA
  have hA' : BB6.Agent3.CReach
      (130+208*(128*w+5)) (94+152*(128*w+5)) := by
    have hx : 130+208*(128*w+5)=1170+26624*w := by omega
    have hy : 94+152*(128*w+5)=854+19456*w := by omega
    simpa only [hx,hy] using hA
  rcases mzero_odd_sumzero_reach_parents (128*w+5) (by omega) hA' with hL | hB
  · have hL' : BB6.Agent3.CReach
      (2022+46080*w) (426+9728*w) := by
        have hx : 222+360*(128*w+5)=2022+46080*w := by omega
        have hy : 46+76*(128*w+5)=426+9728*w := by omega
        simpa only [hx,hy] using hL
    exact blank_no_mzero_L_359 w hL'
  · have hB' : BB6.Agent3.CReach
      (504+11520*w) (1182+27008*w) := by
        have hx : 54+90*(128*w+5)=504+11520*w := by omega
        have hy : 127+211*(128*w+5)=1182+27008*w := by omega
        simpa only [hx,hy] using hB
    exact blank_no_mzero_B_359 w hB'

/-- Original-blank high stopping targets with j=1895 mod 2048 are
    unreachable at all times. The stop equation fixes k, two exact
    inverse edges reach A_(32v+29), and its two source-parent branches
    are both eliminated above. -/
theorem high_stop_mzero_1895 (j k : Nat)
    (hj : j%2048=1895)
    (hstop : k+j+3*0+5=(2:Nat)^(2*0+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  let v := (j-1895)/2048
  have hjform : j=1895+2048*v := by dsimp [v]; omega
  have hp : (2:Nat)^(2*0+2)=4 := by decide
  rw [hp] at hstop
  have htform : j=7+32*(64*v+59) := by omega
  have hkform : k=28+96*(64*v+59) := by omega
  have hxform : 2*j+3=17+64*(64*v+59) := by omega
  intro hr
  have hstart : BB6.Agent3.CReach
      (17+64*(64*v+59)) (28+96*(64*v+59)) := by
    simpa only [hxform,hkform] using hr
  have hA := mzero_first_two_reach (64*v+59) hstart
  have hx : 26+104*(64*v+59)=6162+6656*v := by omega
  have hy : 18+76*(64*v+59)=4502+4864*v := by omega
  have hA' : BB6.Agent3.CReach (6162+6656*v) (4502+4864*v) := by
    simpa only [hx,hy] using hA
  exact blank_no_mzero_t59_ray v hA'

/-- Original-blank high stopping targets with j=359 mod 8192 are
    unreachable at all times. -/
theorem high_stop_mzero_359 (j k : Nat)
    (hj : j%8192=359)
    (hstop : k+j+3*0+5=(2:Nat)^(2*0+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  let w := (j-359)/8192
  have hjform : j=359+8192*w := by dsimp [w]; omega
  have hp : (2:Nat)^(2*0+2)=4 := by decide
  rw [hp] at hstop
  have htform : j=7+32*(256*w+11) := by omega
  have hkform : k=28+96*(256*w+11) := by omega
  have hxform : 2*j+3=17+64*(256*w+11) := by omega
  intro hr
  have hstart : BB6.Agent3.CReach
      (17+64*(256*w+11)) (28+96*(256*w+11)) := by
    simpa only [hxform,hkform] using hr
  have hA := mzero_first_two_reach (256*w+11) hstart
  have hx : 26+104*(256*w+11)=1170+26624*w := by omega
  have hy : 18+76*(256*w+11)=854+19456*w := by omega
  have hA' : BB6.Agent3.CReach (1170+26624*w) (854+19456*w) := by
    simpa only [hx,hy] using hA
  exact blank_no_mzero_t11_ray w hA'

#print axioms mzero_first_two_reach
#print axioms blank_no_mzero_t59_ray
#print axioms blank_no_mzero_t11_ray
#print axioms high_stop_mzero_1895
#print axioms high_stop_mzero_359

end BB6.Agent11M0SumZero
