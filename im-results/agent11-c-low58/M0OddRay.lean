import OddOddVal3Orbit
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0Ray
open BB6.Agent46

/-- Four forced exact original-section inverse edges lead every target
    (145+256q,220+384q) to (484+872q,41+76q). The latter has odd
    right coordinate >=5 and sum =1 mod4, so it is forbidden on the
    authentic blank section orbit. This closes infinitely many m=0
    second-family stopping candidates without a run-time cutoff. -/
theorem blank_no_ray (q : Nat) :
    ¬ BB6.Agent3.CReach (145+256*q) (220+384*q) := by
  intro hr
  have hp1 := (six_even_right_blank_reach_iff
    (145+256*q) (220+384*q)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have h1 : BB6.Agent3.CReach (363+640*q) (109+192*q) := by
    have hx : (145+256*q)+(220+384*q)-2=363+640*q := by omega
    have hy : ((220+384*q)-2)/2=109+192*q := by omega
    simpa only [hx,hy] using hp1

  have hp2 := (BB6.Agent3.oddodd_val3_blank_reach_iff
    (363+640*q) (109+192*q)
    (by omega) (by omega) (by omega) (by omega) (by omega)).mp h1
  have h2 : BB6.Agent3.CReach (234+416*q) (170+304*q) := by
    have hx : ((363+640*q)+(109+192*q)-4)/2=234+416*q := by omega
    have hy : ((363+640*q)+3*(109+192*q)-10)/4=170+304*q := by omega
    simpa only [hx,hy] using hp2

  have hp3 := (six_even_right_blank_reach_iff
    (234+416*q) (170+304*q)
    (by omega) (by omega) (by omega) (by omega)).mp h2
  have h3 : BB6.Agent3.CReach (402+720*q) (84+152*q) := by
    have hx : (234+416*q)+(170+304*q)-2=402+720*q := by omega
    have hy : ((170+304*q)-2)/2=84+152*q := by omega
    simpa only [hx,hy] using hp3

  have hp4 := (six_even_right_blank_reach_iff
    (402+720*q) (84+152*q)
    (by omega) (by omega) (by omega) (by omega)).mp h3
  have h4 : BB6.Agent3.CReach (484+872*q) (41+76*q) := by
    have hx : (402+720*q)+(84+152*q)-2=484+872*q := by omega
    have hy : ((84+152*q)-2)/2=41+76*q := by omega
    simpa only [hx,hy] using hp4

  rcases h4 with ⟨time,ht⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
  | succ n =>
      have hh := BB6.Agent3.blank_section_odd_image n
        (484+872*q) (41+76*q) ht (by omega) (by omega)
      omega

/-- Pullback to the authentic high-stopping equation at m=0:
    j = 71 modulo 128 is a complete infinite blank-unreachable ray. -/
theorem high_stop_mzero_71 (j k : Nat)
    (hj : j%128=71)
    (hstop : k+j+3*0+5=(2:Nat)^(2*0+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  let q := (j-71)/128
  have hjform : j=71+128*q := by dsimp [q]; omega
  have hp : (2:Nat)^(2*0+2)=4 := by decide
  rw [hp] at hstop
  have hkform : k=220+384*q := by omega
  have hxform : 2*j+3=145+256*q := by omega
  rw [hxform,hkform]
  exact blank_no_ray q

#print axioms blank_no_ray
#print axioms high_stop_mzero_71

end BB6.Agent11M0Ray
