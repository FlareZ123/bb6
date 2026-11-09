import OddOddVal3Orbit
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0Four
open BB6.Agent46

/-- A reusable four-edge true-blank predecessor reduction for a quarter
    of the m=0 high stopping family, with unrestricted integer t. The
    inverse sources are individually unique, and their exact source
    conditions follow from t divisible by four. This does not itself
    imply nonreachability of the residual state. -/
theorem mzero_four_reach (t : Nat) (ht : t%4=0)
    (hr : BB6.Agent3.CReach (17+64*t) (28+96*t)) :
    BB6.Agent3.CReach (48+218*t) (3+19*t) := by
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

  have hp3 := (six_even_right_blank_reach_iff
    (26+104*t) (18+76*t)
    (by omega) (by omega) (by omega) (by omega)).mp h2
  have h3 : BB6.Agent3.CReach (42+180*t) (8+38*t) := by
    have hx : (26+104*t)+(18+76*t)-2=42+180*t := by omega
    have hy : ((18+76*t)-2)/2=8+38*t := by omega
    simpa only [hx,hy] using hp3

  have hp4 := (six_even_right_blank_reach_iff
    (42+180*t) (8+38*t)
    (by omega) (by omega) (by omega) (by omega)).mp h3
  have h4 : BB6.Agent3.CReach (48+218*t) (3+19*t) := by
    have hx : (42+180*t)+(8+38*t)-2=48+218*t := by omega
    have hy : ((8+38*t)-2)/2=3+19*t := by omega
    simpa only [hx,hy] using hp4
  exact h4

#print axioms mzero_four_reach

end BB6.Agent11M0Four
