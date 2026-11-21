import RRoot32ParentFanQ
import EvenOddSumPlusOneV3
import M0EvenEvenSumZero
import OddOddLowVal
import EvenRightUnique
import HighSumTwo
import Agent3CImage
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

namespace BB6.Agent3RRoot32ExceptionalCoreQ
open BB6.Agent46

def RunReach (x y : Nat) : Prop :=
  ∃ n, BB6.Agent8Section.run secNext n (some (5,1)) = some (x,y)

theorem run_parent_of_left_gt5 (x y : Nat) (hx : 5<x)
    (hr : RunReach x y) :
    ∃ a k, RunReach a k ∧ secNext (a,k)=some (x,y) := by
  rcases hr with ⟨time,ht⟩
  cases time with
  | zero => simp [BB6.Agent8Section.run] at ht; omega
  | succ n =>
    cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at ht
    | some p =>
      rcases p with ⟨a,k⟩
      refine ⟨a,k,⟨n,hp⟩,?_⟩
      simpa [BB6.Agent8Section.run,hp] using ht

theorem run_no_odd_sum_one (x y : Nat)
    (_hx : 5<x) (hy : 5≤y) (ho : y%2=1)
    (hsum : (x+y)%4=1) : ¬ RunReach x y := by
  intro hr
  have hC : BB6.Agent3.CReach x y := by simpa [RunReach,BB6.Agent3.CReach] using hr
  exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one x y (by omega) hy ho hsum hC

theorem run_no_odd_sum_two (x y : Nat)
    (_hx : 5<x) (hy : 5≤y) (ho : y%2=1)
    (hsum : (x+y)%4=2) : ¬ RunReach x y := by
  intro hr
  have hC : BB6.Agent3.CReach x y := by simpa [RunReach,BB6.Agent3.CReach] using hr
  exact BB6.Agent11High.blank_no_odd_sum_two x y hy ho hsum hC

def P1x (m : Nat) : Nat := 768039162240*m+93809277604
def P1y (m : Nat) : Nat := 517923551040*m+63259839556
def S0 (m : Nat) : Nat := 160745339160*m+19633639645
def Dx (m : Nat) : Nat := 1285962713280*m+157069117158
def Dy (m : Nat) : Nat := 258961775520*m+31629919777
def Ex (m : Nat) : Nat := 321490678320*m+39267279288
def Ey (m : Nat) : Nat := 741197793000*m+90530838709
def Ax (m : Nat) : Nat := 772462244400*m+94349518465
def Ay (m : Nat) : Nat := 515712009960*m+62989719120
def Xx (m : Nat) : Nat := 1288174254360*m+157339237583
def Xy (m : Nat) : Nat := 257856004980*m+31494859559

theorem R_unreachable_q7 (q : Nat) (hq : q%64=7) :
    ¬ RunReach (BB6.Agent3RRoot32ParentFanQ.RxQ q)
      (BB6.Agent3RRoot32ParentFanQ.RyQ q) := by
  intro hR
  let m := q/64
  have hqeq : q=64*m+7 := by dsimp [m]; omega
  obtain ⟨a,k,hprev,hedge⟩ := run_parent_of_left_gt5
    (BB6.Agent3RRoot32ParentFanQ.RxQ q)
    (BB6.Agent3RRoot32ParentFanQ.RyQ q) (by dsimp [BB6.Agent3RRoot32ParentFanQ.RxQ]; omega) hR
  rcases BB6.Agent3RRoot32ParentFanQ.R_parent_fan_q7 q a k hq hedge with hdirect | hbounce
  · have hRpreach : RunReach
        (BB6.Agent3RRoot32ParentFanQ.RpxQ q)
        (BB6.Agent3RRoot32ParentFanQ.RpyQ q) := by
      simpa [hdirect] using hprev
    have hpx : BB6.Agent3RRoot32ParentFanQ.RpxQ q%2=1 := by rw [hqeq]; dsimp [BB6.Agent3RRoot32ParentFanQ.RpxQ]; omega
    have hpy : BB6.Agent3RRoot32ParentFanQ.RpyQ q%2=1 := by rw [hqeq]; dsimp [BB6.Agent3RRoot32ParentFanQ.RpyQ]; omega
    have hpy5 : 5≤BB6.Agent3RRoot32ParentFanQ.RpyQ q := by rw [hqeq]; dsimp [BB6.Agent3RRoot32ParentFanQ.RpyQ]; omega
    have hsum4 : (BB6.Agent3RRoot32ParentFanQ.RpxQ q+BB6.Agent3RRoot32ParentFanQ.RpyQ q)%4=0 := by
      rw [hqeq]
      dsimp [BB6.Agent3RRoot32ParentFanQ.RpxQ,BB6.Agent3RRoot32ParentFanQ.RpyQ]
      omega
    have hsum16 : (BB6.Agent3RRoot32ParentFanQ.RpxQ q+BB6.Agent3RRoot32ParentFanQ.RpyQ q)%16=12 := by
      rw [hqeq]
      dsimp [BB6.Agent3RRoot32ParentFanQ.RpxQ,BB6.Agent3RRoot32ParentFanQ.RpyQ]
      omega
    have hsize : 24≤BB6.Agent3RRoot32ParentFanQ.RpxQ q+BB6.Agent3RRoot32ParentFanQ.RpyQ q := by
      rw [hqeq]
      dsimp [BB6.Agent3RRoot32ParentFanQ.RpxQ,BB6.Agent3RRoot32ParentFanQ.RpyQ]
      omega
    have hP1reach : RunReach (P1x m) (P1y m) := by
      have hiff := BB6.Agent3.oddodd_lowval_blank_reach_iff
        (BB6.Agent3RRoot32ParentFanQ.RpxQ q)
        (BB6.Agent3RRoot32ParentFanQ.RpyQ q)
        hpx hpy hpy5 hsum4 (by omega) hsize
      have hP1x :
          (BB6.Agent3RRoot32ParentFanQ.RpxQ q+
            BB6.Agent3RRoot32ParentFanQ.RpyQ q-4)/2=P1x m := by
        rw [hqeq]
        dsimp [BB6.Agent3RRoot32ParentFanQ.RpxQ,BB6.Agent3RRoot32ParentFanQ.RpyQ,P1x]
        omega
      have hP1y :
          (BB6.Agent3RRoot32ParentFanQ.RpxQ q+
            3*BB6.Agent3RRoot32ParentFanQ.RpyQ q-10)/4=P1y m := by
        rw [hqeq]
        dsimp [BB6.Agent3RRoot32ParentFanQ.RpxQ,BB6.Agent3RRoot32ParentFanQ.RpyQ,P1y]
        omega
      simpa [RunReach,hP1x,hP1y] using hiff.mp hRpreach
    have hP1x0 : 0<P1x m := by dsimp [P1x]; omega
    have hP1xe : P1x m%2=0 := by dsimp [P1x]; omega
    have hP1y6 : 6≤P1y m := by dsimp [P1y]; omega
    have hP1ye : P1y m%2=0 := by dsimp [P1y]; omega
    have hP1sum : P1x m+P1y m=8*S0 m := by dsimp [P1x,P1y,S0]; omega
    have hS04 : S0 m%4≠0 := by dsimp [S0]; omega
    have hS0gt : 2<S0 m := by dsimp [S0]; omega
    obtain ⟨ap,kp,hP1prev,hP1edge⟩ := run_parent_of_left_gt5
      (P1x m) (P1y m) (by dsimp [P1x]; omega) hP1reach
    have hfan := BB6.Agent11M0SumZeroVerified.even_even_sumzero_parent
      ap kp (P1x m) (P1y m) (S0 m)
      hP1x0 hP1xe hP1y6 hP1ye hP1sum hS04 hS0gt hP1edge
    rcases hfan with hD | hE
    · have hDreach : RunReach (Dx m) (Dy m) := by
        rcases hD with ⟨ha,hk⟩
        have hDx : P1x m+P1y m-2=Dx m := by dsimp [P1x,P1y,Dx]; omega
        have hDy : (P1y m-2)/2=Dy m := by dsimp [P1y,Dy]; omega
        simpa [ha,hk,hDx,hDy] using hP1prev
      have hDplus16 : (Dx m+Dy m+1)%16=8 := by dsimp [Dx,Dy]; omega
      have hAreach : RunReach (Ax m) (Ay m) := by
        obtain ⟨ad,kd,hDprev,hDedge⟩ := run_parent_of_left_gt5
          (Dx m) (Dy m) (by dsimp [Dx]; omega) hDreach
        have hparent := BB6.Agent3EvenOddV3Parent.evenodd_sumplusone_v3_parent
          (Dx m) (Dy m) ad kd
          (by dsimp [Dx]; omega) (by dsimp [Dx]; omega)
          (by dsimp [Dy]; omega) (by dsimp [Dy]; omega) hDplus16 hDedge
        rcases hparent with ⟨had,hkd⟩
        have hAx : (Dx m+Dy m+1)/2-3=Ax m := by dsimp [Dx,Dy,Ax]; omega
        have hAy : (Dx m+2*Dy m-Ax m-7)/2=Ay m := by dsimp [Dx,Dy,Ax,Ay]; omega
        simpa [had,hkd,hAx,hAy] using hDprev
      have hAyeven : Ay m%2=0 := by dsimp [Ay]; omega
      have hAy6 : 6≤Ay m := by dsimp [Ay]; omega
      have hAsum8 : (Ax m+Ay m)%8=1 := by dsimp [Ax,Ay]; omega
      have hXreach : RunReach (Xx m) (Xy m) := by
        have hiff := BB6.Agent15.blank_reach_iff_even_right
          (Ax m) (Ay m) hAy6 hAyeven (by omega) (by omega)
        have hXx : Ax m+Ay m-2=Xx m := by dsimp [Ax,Ay,Xx]; omega
        have hXy : (Ay m-2)/2=Xy m := by dsimp [Ay,Xy]; omega
        simpa [RunReach,hXx,hXy] using hiff.mp hAreach
      have hXx5 : 5<Xx m := by dsimp [Xx]; omega
      have hXy5 : 5≤Xy m := by dsimp [Xy]; omega
      have hXyodd : Xy m%2=1 := by dsimp [Xy]; omega
      have hXsum2 : (Xx m+Xy m)%4=2 := by dsimp [Xx,Xy]; omega
      exact (run_no_odd_sum_two (Xx m) (Xy m) hXx5 hXy5 hXyodd hXsum2) hXreach
    · have hEreach : RunReach (Ex m) (Ey m) := by
        rcases hE with ⟨ha,hk⟩
        have hEx : 2*S0 m-2=Ex m := by dsimp [S0,Ex]; omega
        have hEy : (P1x m+2*P1y m-2*S0 m-8)/2=Ey m := by dsimp [P1x,P1y,S0,Ey]; omega
        simpa [ha,hk,hEx,hEy] using hP1prev
      have hEx5 : 5<Ex m := by dsimp [Ex]; omega
      have hEy5 : 5≤Ey m := by dsimp [Ey]; omega
      have hEyodd : Ey m%2=1 := by dsimp [Ey]; omega
      have hEsum1 : (Ex m+Ey m)%4=1 := by dsimp [Ex,Ey]; omega
      exact (run_no_odd_sum_one (Ex m) (Ey m) hEx5 hEy5 hEyodd hEsum1) hEreach
  · have hAreach : RunReach
        (BB6.Agent3RRoot32ParentFanQ.AbxQ q)
        (BB6.Agent3RRoot32ParentFanQ.AbyQ q) := by
      simpa [hbounce] using hprev
    have hAby5 : 5≤BB6.Agent3RRoot32ParentFanQ.AbyQ q := by
      rw [hqeq]
      dsimp [BB6.Agent3RRoot32ParentFanQ.AbyQ]
      omega
    have hAbyodd : BB6.Agent3RRoot32ParentFanQ.AbyQ q%2=1 := by
      rw [hqeq]
      dsimp [BB6.Agent3RRoot32ParentFanQ.AbyQ]
      omega
    have hAsum2 :
        (BB6.Agent3RRoot32ParentFanQ.AbxQ q+
          BB6.Agent3RRoot32ParentFanQ.AbyQ q)%4=2 := by
      rw [hqeq]
      dsimp [BB6.Agent3RRoot32ParentFanQ.AbxQ,BB6.Agent3RRoot32ParentFanQ.AbyQ]
      omega
    exact (run_no_odd_sum_two
      (BB6.Agent3RRoot32ParentFanQ.AbxQ q)
      (BB6.Agent3RRoot32ParentFanQ.AbyQ q)
      (by rw [hqeq]; dsimp [BB6.Agent3RRoot32ParentFanQ.AbxQ]; omega)
      hAby5 hAbyodd hAsum2) hAreach

#print axioms R_unreachable_q7

end BB6.Agent3RRoot32ExceptionalCoreQ
