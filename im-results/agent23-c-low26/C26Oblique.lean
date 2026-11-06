import OddOddLowVal
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent23C26
open BB6.Agent3 BB6.Agent46

/-- Two modular inverse cylinders, written with positive affine parameters. -/
theorem blank_no_eeoee_pattern (x q z : Nat)
    (hx : x+2*z=16*q+7) (hz : 4≤z)
    (hcase : (z%4=3 ∧ q%4=0) ∨ (z%4=2 ∧ q%4=3)) :
    ¬ BB6.Agent3.CReach x (8*z+2) := by
  intro h
  have h1 : BB6.Agent3.CReach (x+8*z) (4*z) := by
    have hh := (six_even_right_blank_reach_iff x (8*z+2)
      (by omega) (by omega) (by omega) (by omega)).mp h
    have ha : x+(8*z+2)-2=x+8*z := by omega
    have hb : ((8*z+2)-2)/2=4*z := by omega
    simpa only [ha,hb] using hh
  have h2 : BB6.Agent3.CReach (x+12*z-2) (2*z-1) := by
    have hh := (six_even_right_blank_reach_iff (x+8*z) (4*z)
      (by omega) (by omega) (by omega) (by omega)).mp h1
    have ha : (x+8*z)+(4*z)-2=x+12*z-2 := by omega
    have hb : ((4*z)-2)/2=2*z-1 := by omega
    simpa only [ha,hb] using hh
  have h3 : BB6.Agent3.CReach (8*q+6*z) (4*q+4*z-2) := by
    have hh := (oddodd_lowval_blank_reach_iff (x+12*z-2) (2*z-1)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp h2
    have ha : ((x+12*z-2)+(2*z-1)-4)/2=8*q+6*z := by omega
    have hb : ((x+12*z-2)+3*(2*z-1)-10)/4=4*q+4*z-2 := by omega
    simpa only [ha,hb,BB6.Agent3.CReach] using hh
  have h4 : BB6.Agent3.CReach (12*q+10*z-4) (2*q+2*z-2) := by
    have hh := (six_even_right_blank_reach_iff (8*q+6*z) (4*q+4*z-2)
      (by omega) (by omega) (by omega) (by omega)).mp h3
    have ha : (8*q+6*z)+(4*q+4*z-2)-2=12*q+10*z-4 := by omega
    have hb : ((4*q+4*z-2)-2)/2=2*q+2*z-2 := by omega
    simpa only [ha,hb] using hh
  have h5 : BB6.Agent3.CReach (14*q+12*z-8) (q+z-2) := by
    have hh := (six_even_right_blank_reach_iff (12*q+10*z-4) (2*q+2*z-2)
      (by omega) (by omega) (by omega) (by omega)).mp h4
    have ha : (12*q+10*z-4)+(2*q+2*z-2)-2=14*q+12*z-8 := by omega
    have hb : ((2*q+2*z-2)-2)/2=q+z-2 := by omega
    simpa only [ha,hb] using hh
  rcases h5 with ⟨n,hn⟩
  cases n with
  | zero =>
      simp [BB6.Agent8Section.run] at hn
      omega
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n
        (14*q+12*z-8) (q+z-2) hn (by omega) (by omega)
      omega

/-- Two modular original-section forbidden sets with an explicit small-state cutoff. -/
theorem blank_no_oblique_mod256 (x y : Nat) (hy : 34≤y)
    (hmod : (y%32=26 ∧ (4*x+y)%256=30) ∨
            (y%32=18 ∧ (4*x+y)%256=222)) :
    ¬ BB6.Agent3.CReach x y := by
  let z := (y-2)/8
  have hyform : y=8*z+2 := by dsimp [z]; omega
  have hz : 4≤z := by dsimp [z]; omega
  let q := (x+2*z-7)/16
  have hx : x+2*z=16*q+7 := by dsimp [q,z]; omega
  have hcase : (z%4=3 ∧ q%4=0) ∨ (z%4=2 ∧ q%4=3) := by
    dsimp [q,z]
    omega
  rw [hyform]
  exact blank_no_eeoee_pattern x q z hx hz hcase

#print axioms blank_no_oblique_mod256
#print axioms blank_no_eeoee_pattern
end BB6.Agent23C26
