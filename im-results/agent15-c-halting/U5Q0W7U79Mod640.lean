import U5Q0W7U19Mod2560
import MixedOdd16TwoOrbit
import M0EvenEvenSumZero
import Lean.Elab.Tactic.Omega

/-!
# U5 w=7: a source-exact subcylinder of the u = 79 (mod 80) residual

For u = 239 + 640*r, the q=1 odd/odd parent lies in the exact sum-16
two-parent sector. Both parents are even/even; the complete six-even-right
inverse sends them to the source-proved odd-right sum-one forbidden image.
The generic U5 q=0 parent-fan theorem then excludes the corresponding q=0
target. This is an infinite intermediate Machine C nonreachability family,
not a Machine C decision or a BB(6) upper bound.
-/

namespace BB6.Agent15U5W7U79
open BB6.Agent46

private theorem even_right_parent_of_reach (x y : Nat)
    (hy : 6≤y) (he : y%2=0)
    (h0 : (x+y)%8≠0) (h7 : (x+y)%8≠7) :
    BB6.Agent3.CReach x y →
      BB6.Agent3.CReach (x+y-2) ((y-2)/2) :=
  (BB6.Agent46.six_even_right_blank_reach_iff x y hy he h0 h7).mp

/-- The first sum-16 parent is excluded after three exact source inverses. -/
private theorem q1_p0_unreachable (r : Nat) :
    ¬ BB6.Agent3.CReach
      (5583030+14911680*r) (7514070+20069280*r) := by
  intro hP0
  have hD0 : BB6.Agent3.CReach
      (13097098+34980960*r) (3757034+10034640*r) := by
    have h := even_right_parent_of_reach
      (5583030+14911680*r) (7514070+20069280*r)
      (by omega) (by omega) (by omega) (by omega) hP0
    have hx :
        (5583030+14911680*r)+(7514070+20069280*r)-2 =
          13097098+34980960*r := by omega
    have hy :
        ((7514070+20069280*r)-2)/2 = 3757034+10034640*r := by omega
    simpa only [hx,hy] using h
  have hD1 : BB6.Agent3.CReach
      (16854130+45015600*r) (1878516+5017320*r) := by
    have h := even_right_parent_of_reach
      (13097098+34980960*r) (3757034+10034640*r)
      (by omega) (by omega) (by omega) (by omega) hD0
    have hx :
        (13097098+34980960*r)+(3757034+10034640*r)-2 =
          16854130+45015600*r := by omega
    have hy :
        ((3757034+10034640*r)-2)/2 = 1878516+5017320*r := by omega
    simpa only [hx,hy] using h
  have hD2 : BB6.Agent3.CReach
      (18732644+50032920*r) (939257+2508660*r) := by
    have h := even_right_parent_of_reach
      (16854130+45015600*r) (1878516+5017320*r)
      (by omega) (by omega) (by omega) (by omega) hD1
    have hx :
        (16854130+45015600*r)+(1878516+5017320*r)-2 =
          18732644+50032920*r := by omega
    have hy :
        ((1878516+5017320*r)-2)/2 = 939257+2508660*r := by omega
    simpa only [hx,hy] using h
  exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    (18732644+50032920*r) (939257+2508660*r)
    (by omega) (by omega) (by omega) (by omega) hD2

/-- The second sum-16 parent is excluded by one exact source inverse. -/
private theorem q1_p2_unreachable (r : Nat) :
    ¬ BB6.Agent3.CReach
      (1395756+3727920*r) (9607704+25661160*r) := by
  intro hP2
  have hE2 : BB6.Agent3.CReach
      (11003458+29389080*r) (4803851+12830580*r) := by
    have h := even_right_parent_of_reach
      (1395756+3727920*r) (9607704+25661160*r)
      (by omega) (by omega) (by omega) (by omega) hP2
    have hx :
        (1395756+3727920*r)+(9607704+25661160*r)-2 =
          11003458+29389080*r := by omega
    have hy :
        ((9607704+25661160*r)-2)/2 = 4803851+12830580*r := by omega
    simpa only [hx,hy] using h
  exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    (11003458+29389080*r) (4803851+12830580*r)
    (by omega) (by omega) (by omega) (by omega) hE2

/-- The q=1 parent Q(u) is blank-unreachable for u = 239 (mod 640). -/
theorem w7_q1_parent_unreachable_u239mod640 (r : Nat) :
    ¬ BB6.Agent3.CReach
      (1720951+4596480*r) (9445113+25226880*r) := by
  intro hA
  have hFan := (BB6.Agent3.oddodd_sum16_blank_reach_iff
    (1720951+4596480*r) (9445113+25226880*r)
    (by omega) (by omega) (by omega) (by omega)).mp hA
  rcases hFan with hP0 | hP2
  · have hx :
        ((1720951+4596480*r)+(9445113+25226880*r)-4)/2 =
          5583030+14911680*r := by omega
    have hy :
        ((1720951+4596480*r)+3*(9445113+25226880*r)-10)/4 =
          7514070+20069280*r := by omega
    have hP0' : BB6.Agent3.CReach
        (5583030+14911680*r) (7514070+20069280*r) := by
      simpa only [hx,hy] using hP0
    exact q1_p0_unreachable r hP0'
  · have hx :
        ((1720951+4596480*r)+(9445113+25226880*r)-16)/8 =
          1395756+3727920*r := by omega
    have hy :
        (7*(1720951+4596480*r)+15*(9445113+25226880*r)-88)/16 =
          9607704+25661160*r := by omega
    have hP2' : BB6.Agent3.CReach
        (1395756+3727920*r) (9607704+25661160*r) := by
      simpa only [hx,hy] using hP2
    exact q1_p2_unreachable r hP2'

/-- The q=0 U5 target is unreachable on the infinite cylinder u=239+640*r. -/
theorem w7_q0_target_unreachable_u239mod640 (r : Nat) :
    ¬ BB6.Agent3.CReach
      (6924072+18493440*r) (6843559+18278400*r) := by
  let u : Nat := 239+640*r
  have huodd : u%2=1 := by dsimp [u]; omega
  have hq1 : ¬ BB6.Agent3.CReach
      (2*(2228+3591*u)-3) (24450+39417*u) := by
    have hx : 2*(2228+3591*u)-3 =
        1720951+4596480*r := by dsimp [u]; omega
    have hy : 24450+39417*u =
        9445113+25226880*r := by dsimp [u]; omega
    intro h
    have h' : BB6.Agent3.CReach
        (1720951+4596480*r) (9445113+25226880*r) := by
      simpa only [hx,hy] using h
    exact w7_q1_parent_unreachable_u239mod640 r h'
  have h := BB6.Agent15U5W7Source.w7_q0_target_unreachable_of_q1 u huodd hq1
  have hx : 17928+28896*u = 6924072+18493440*r := by dsimp [u]; omega
  have hy : 17719+28560*u = 6843559+18278400*r := by dsimp [u]; omega
  simpa only [hx,hy] using h

#print axioms w7_q1_parent_unreachable_u239mod640
#print axioms w7_q0_target_unreachable_u239mod640

end BB6.Agent15U5W7U79
