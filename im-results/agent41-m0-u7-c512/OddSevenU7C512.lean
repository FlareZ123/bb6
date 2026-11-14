import M0EvenEvenSumZero
import OddSevenSliver
import OddEvenInverse
import EvenRightSixOrbit
import OddOddLowVal
import EvenOddFourExact
import HighSumTwo
import Lean.Elab.Tactic.Omega

namespace BB6.Agent41U7C512
open BB6.Agent46

private theorem oddeven_sum3_parent_reach (x y : Nat)
    (hxgt : 5 < x) (hy : 6 ≤ y)
    (hx : x % 2 = 1) (he : y % 2 = 0)
    (hs : (x+y) % 8 = 3)
    (hr : BB6.Agent3.CReach x y) :
    BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 x y hxgt hr
  have hform := section_oddeven_sum3_mod8_inverse
    a k x y hy hx he hs hstep
  have ha : a=x+y-2 := hform.1
  have hk : k=(y-2)/2 := hform.2
  simpa only [ha,hk] using hprev

private theorem e4_parent (d : Nat)
    (hr : BB6.Agent3.CReach
      (186982898+239975840*d) (11087493+14229808*d)) :
    BB6.Agent3.CReach
      (99035193+127102824*d) (55061342+70666316*d) := by
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (186982898+239975840*d) (11087493+14229808*d)
      (by omega) hr
  have hform := (BB6.Agent3.odd_seven_parent_iff
    a k (186982898+239975840*d) (11087493+14229808*d)
    (by omega) (by omega) (by omega) (by omega) (by omega)).mp hstep
  have ha : a=99035193+127102824*d := by omega
  have hk : k=55061342+70666316*d := by omega
  simpa only [ha,hk] using hprev

/-- A second disjoint infinite subfamily of the u=64*c+7 residual:
    c=512*g+7. The exact original-section inverse chain ends in the
    source-forbidden odd/odd sum-two sector. -/
theorem u7_E4_unreachable_c512 (g : Nat) :
    ¬ BB6.Agent3.CReach
      (7001018+59993960*(512*g+7))
      (415137+3557452*(512*g+7)) := by
  let d := 128*g+1
  intro hE
  have hxE :
      7001018+59993960*(512*g+7)=186982898+239975840*d := by
    dsimp [d]
    omega
  have hyE :
      415137+3557452*(512*g+7)=11087493+14229808*d := by
    dsimp [d]
    omega
  have hE' : BB6.Agent3.CReach
      (186982898+239975840*d) (11087493+14229808*d) := by
    simpa only [hxE,hyE] using hE
  have hP0d := e4_parent d hE'
  let x0 := 226138017+16269161472*g
  let y0 := 125727658+9045288448*g
  have hx0 : 99035193+127102824*d=x0 := by
    dsimp [x0,d]
    omega
  have hy0 : 55061342+70666316*d=y0 := by
    dsimp [y0,d]
    omega
  have hP0 : BB6.Agent3.CReach x0 y0 := by
    simpa only [hx0,hy0] using hP0d

  have hP1raw := oddeven_sum3_parent_reach x0 y0
    (by dsimp [x0]; omega) (by dsimp [y0]; omega)
    (by dsimp [x0]; omega) (by dsimp [y0]; omega)
    (by dsimp [x0,y0]; omega) hP0
  let x1 := 351865673+25314449920*g
  let y1 := 62863828+4522644224*g
  have hx1 : x0+y0-2=x1 := by dsimp [x0,y0,x1]; omega
  have hy1 : (y0-2)/2=y1 := by dsimp [y0,y1]; omega
  have hP1 : BB6.Agent3.CReach x1 y1 := by
    simpa only [hx1,hy1] using hP1raw

  have hP2raw := (six_even_right_blank_reach_iff
    x1 y1 (by dsimp [y1]; omega) (by dsimp [y1]; omega)
    (by dsimp [x1,y1]; omega) (by dsimp [x1,y1]; omega)).mp hP1
  let x2 := 414729499+29837094144*g
  let y2 := 31431913+2261322112*g
  have hx2 : x1+y1-2=x2 := by dsimp [x1,y1,x2]; omega
  have hy2 : (y1-2)/2=y2 := by dsimp [y1,y2]; omega
  have hP2 : BB6.Agent3.CReach x2 y2 := by
    simpa only [hx2,hy2] using hP2raw

  have hP3raw := (oddodd_lowval_blank_reach_iff
    x2 y2 (by dsimp [x2]; omega) (by dsimp [y2]; omega)
    (by dsimp [y2]; omega) (by dsimp [x2,y2]; omega)
    (by dsimp [x2,y2]; omega) (by dsimp [x2,y2]; omega)).mp hP2
  let x3 := 223080704+16049208128*g
  let y3 := 127256307+9155265120*g
  have hx3 : (x2+y2-4)/2=x3 := by dsimp [x2,y2,x3]; omega
  have hy3 : (x2+3*y2-10)/4=y3 := by dsimp [x2,y2,y3]; omega
  have hP3 : BB6.Agent3.CReach x3 y3 := by
    simpa only [hx3,hy3] using hP3raw

  have hP4raw := (evenodd_four_blank_reach_iff
    x3 y3 (by dsimp [x3]; omega) (by dsimp [y3]; omega)
    (by dsimp [y3]; omega) (by dsimp [x3,y3]; omega)).mp hP3
  let x4 := 175168503+12602236624*g
  let y4 := 151212404+10878750872*g
  have hx4 : (x3+y3-5)/2=x4 := by dsimp [x3,y3,x4]; omega
  have hy4 : (x3+3*y3-9)/4=y4 := by dsimp [x3,y3,y4]; omega
  have hP4 : BB6.Agent3.CReach x4 y4 := by
    simpa only [hx4,hy4] using hP4raw

  have hP5raw := oddeven_sum3_parent_reach x4 y4
    (by dsimp [x4]; omega) (by dsimp [y4]; omega)
    (by dsimp [x4]; omega) (by dsimp [y4]; omega)
    (by dsimp [x4,y4]; omega) hP4
  let x5 := 326380905+23480987496*g
  let y5 := 75606201+5439375436*g
  have hx5 : x4+y4-2=x5 := by dsimp [x4,y4,x5]; omega
  have hy5 : (y4-2)/2=y5 := by dsimp [y4,y5]; omega
  have hP5 : BB6.Agent3.CReach x5 y5 := by
    simpa only [hx5,hy5] using hP5raw

  exact (BB6.Agent11High.blank_no_odd_sum_two x5 y5
    (by dsimp [y5]; omega) (by dsimp [y5]; omega)
    (by dsimp [x5,y5]; omega)) hP5

#print axioms u7_E4_unreachable_c512
end BB6.Agent41U7C512
