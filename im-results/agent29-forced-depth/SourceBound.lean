import FullForcedNormalize
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0

namespace BB6.Agent29Depth
open BB6.Agent3

/-- Exactly the three unique, source-proved inverse sectors of Machine C.
    The order agrees with FullForcedNormalize because the guards are disjoint. -/
def forcedEdge (x y u v : Nat) : Prop :=
  (oddLowGate x y ∧ u = (x+y-4)/2 ∧ v = (x+3*y-10)/4) ∨
  (evenSevenGate x y ∧ u = (x+y-5)/2 ∧ v = (x+3*y-9)/4) ∨
  (evenAffineGate x y ∧ u = x+y-2 ∧ v = (y-2)/2)

/-- The first four steps may exist, but a fifth is arithmetically impossible
    in the entire weighted-mass class one modulo four, with no size cutoff. -/
theorem no_five_mass_one
    (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 : Nat)
    (hm : (x0+2*y0)%4=1)
    (h01 : forcedEdge x0 y0 x1 y1)
    (h12 : forcedEdge x1 y1 x2 y2)
    (h23 : forcedEdge x2 y2 x3 y3)
    (h34 : forcedEdge x3 y3 x4 y4)
    (h45 : forcedEdge x4 y4 x5 y5) : False := by
  simp only [forcedEdge, oddLowGate, evenSevenGate, evenAffineGate] at *
  rcases h01 with h01 | h01 | h01
  all_goals rcases h12 with h12 | h12 | h12
  all_goals rcases h23 with h23 | h23 | h23
  all_goals rcases h34 with h34 | h34 | h34
  all_goals rcases h45 with h45 | h45 | h45
  all_goals omega

/-- For weighted mass zero, the first exact forced inverse must be the
    seven-sector E branch. -/
theorem mass_zero_first_seven (x y u v : Nat)
    (hm : (x+2*y)%4=0)
    (he : forcedEdge x y u v) :
    evenSevenGate x y ∧ u = (x+y-5)/2 ∧ v = (x+3*y-9)/4 := by
  unfold forcedEdge at he
  rcases he with ho | he | ha
  · simp only [oddLowGate] at ho
    omega
  · exact he
  · simp only [evenAffineGate] at ha
    omega

/-- The E predecessor drops weighted mass by seven, changing residue 0 to 1. -/
theorem mass_zero_seven_to_one (x y u v : Nat)
    (hm : (x+2*y)%4=0)
    (he : evenSevenGate x y)
    (hu : u=(x+y-5)/2)
    (hv : v=(x+3*y-9)/4) :
    (u+2*v)%4=1 := by
  simp only [evenSevenGate] at he
  omega

/-- A zero-mass input cannot have six consecutive exact forced inverses. -/
theorem no_six_mass_zero
    (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : Nat)
    (hm : (x0+2*y0)%4=0)
    (h01 : forcedEdge x0 y0 x1 y1)
    (h12 : forcedEdge x1 y1 x2 y2)
    (h23 : forcedEdge x2 y2 x3 y3)
    (h34 : forcedEdge x3 y3 x4 y4)
    (h45 : forcedEdge x4 y4 x5 y5)
    (h56 : forcedEdge x5 y5 x6 y6) : False := by
  obtain ⟨he,hu,hv⟩ := mass_zero_first_seven x0 y0 x1 y1 hm h01
  have hm1 := mass_zero_seven_to_one x0 y0 x1 y1 hm he hu hv
  exact no_five_mass_one x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
    hm1 h12 h23 h34 h45 h56

/-- Class-two weighted mass forces the first step into the seven gate,
    with no large-counter or positive-depth hypothesis. -/
theorem mass_two_first_seven (x y u v : Nat)
    (hm : (x+2*y)%4=2)
    (h : forcedEdge x y u v) :
    evenSevenGate x y ∧
      u=(x+y-5)/2 ∧ v=(x+3*y-9)/4 := by
  unfold forcedEdge at h
  rcases h with ho | he | ha
  · simp only [oddLowGate] at ho
    omega
  · exact he
  · simp only [evenAffineGate] at ha
    omega

/-- Weighted mass congruent to two cannot admit three consecutive
    source-exact forced inverse operations. -/
theorem no_three_mass_two
    (x0 y0 x1 y1 x2 y2 x3 y3 : Nat)
    (hm : (x0+2*y0)%4=2)
    (h01 : forcedEdge x0 y0 x1 y1)
    (h12 : forcedEdge x1 y1 x2 y2)
    (h23 : forcedEdge x2 y2 x3 y3) : False := by
  simp only [forcedEdge,oddLowGate,evenSevenGate,evenAffineGate] at *
  rcases h01 with h01 | h01 | h01
  all_goals rcases h12 with h12 | h12 | h12
  all_goals rcases h23 with h23 | h23 | h23
  all_goals omega

/-- Two is attained on an E O chain in the class-two sector. -/
theorem two_is_sharp :
    forcedEdge 32 7 17 11 ∧ forcedEdge 17 11 12 10 := by
  simp [forcedEdge,oddLowGate,evenSevenGate,evenAffineGate]

/-- Any one-left target with odd right counter can admit at most one
    exact source-forced predecessor, without any stopping equation.
    A first O makes an even first counter; an E successor would
    contradict the O sum modulo sixteen guard. -/
theorem one_left_odd_no_two (y u v p q : Nat)
    (hy : y%2=1)
    (h1 : forcedEdge 1 y u v)
    (h2 : forcedEdge u v p q) : False := by
  simp only [forcedEdge,oddLowGate,evenSevenGate,evenAffineGate] at *
  rcases h1 with h1 | h1 | h1
  all_goals rcases h2 with h2 | h2 | h2
  all_goals omega

/-- An odd/odd second-family input with the necessary stopping equation
    modulo sixteen can never have three exact forced inverse steps.
    No upper bound on the parameters is imposed. -/
theorem oddodd_second_mod16_no_three
    (j m k x1 y1 x2 y2 x3 y3 : Nat)
    (hj : j%2=1) (hm : m%2=1)
    (hmod : (k+j+3*m+5)%16=0)
    (h01 : forcedEdge (2*j+3) k x1 y1)
    (h12 : forcedEdge x1 y1 x2 y2)
    (h23 : forcedEdge x2 y2 x3 y3) : False := by
  simp only [forcedEdge,oddLowGate,evenSevenGate,evenAffineGate] at *
  rcases h01 with h01 | h01 | h01
  all_goals rcases h12 with h12 | h12 | h12
  all_goals rcases h23 with h23 | h23 | h23
  all_goals omega

/-- Every odd-j / odd-m member of the genuine second stopping equation
    has forced inverse depth at most two. -/
theorem oddodd_second_gate_no_three
    (j m k x1 y1 x2 y2 x3 y3 : Nat)
    (hj : j%2=1) (hm : m%2=1)
    (hgate : k+j+3*m+5 = 2^(2*m+2)*(j+3))
    (h01 : forcedEdge (2*j+3) k x1 y1)
    (h12 : forcedEdge x1 y1 x2 y2)
    (h23 : forcedEdge x2 y2 x3 y3) : False := by
  have hPdiv : 16∣2^(2*m+2) := by
    change 2^4∣2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨z,hz⟩ := hPdiv
  have hd : 16∣k+j+3*m+5 := by
    refine ⟨z*(j+3),?_⟩
    calc
      k+j+3*m+5 = 2^(2*m+2)*(j+3) := hgate
      _ = (16*z)*(j+3) := by rw [hz]
      _ = 16*(z*(j+3)) := by ac_rfl
  have hmod : (k+j+3*m+5)%16=0 :=
    Nat.mod_eq_zero_of_dvd hd
  exact oddodd_second_mod16_no_three j m k x1 y1 x2 y2 x3 y3
    hj hm hmod h01 h12 h23

/-- Both universal bounds are attained by genuine, exact guarded inverse
    transitions, although these are synthetic section states rather than
    demonstrated points of the blank orbit. -/
theorem four_is_sharp :
    forcedEdge 569 292564 293131 146281 ∧
    forcedEdge 293131 146281 219704 182991 ∧
    forcedEdge 219704 182991 201345 192167 ∧
    forcedEdge 201345 192167 196754 194459 := by
  simp [forcedEdge, oddLowGate, evenSevenGate, evenAffineGate]

theorem five_is_sharp :
    forcedEdge 6 113 57 84 ∧
    forcedEdge 57 84 139 41 ∧
    forcedEdge 139 41 88 63 ∧
    forcedEdge 88 63 73 67 ∧
    forcedEdge 73 67 68 66 := by
  simp [forcedEdge, oddLowGate, evenSevenGate, evenAffineGate]

#print axioms no_five_mass_one
#print axioms no_six_mass_zero
#print axioms no_three_mass_two
#print axioms two_is_sharp
#print axioms one_left_odd_no_two
#print axioms oddodd_second_mod16_no_three
#print axioms oddodd_second_gate_no_three
#print axioms four_is_sharp
#print axioms five_is_sharp
end BB6.Agent29Depth
