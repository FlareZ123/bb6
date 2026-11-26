import U5Q0W7ParentFan
import EvenRightUnique
import SectionEvenOddSum3Inverse
import OddOddLowVal
import Lean.Elab.Tactic.Omega

/-!
A further exact-source sublift in the z divisible-by-four sector.
For z=1884+2048s, three even-right inverses and the exact even/odd
sum-three parent force an odd/odd low-valuation parent. Its right
coordinate is odd and its sum is one modulo four, so the blank-image
invariant excludes it. This is an intermediate source-composition draft.
-/

namespace BB6.Agent15U5W7R21
open BB6.Agent46

/-- The z=1884 (mod 2048) member of the z=0 (mod 4) sector is blank-unreachable. -/
theorem w7_q0_target_unreachable_z1884mod2048 (s : Nat) :
    ¬ BB6.Agent3.CReach (13613496+14794752*s) (13455199+14622720*s) := by
  let u : Nat := 471+512*s
  let z : Nat := 4*u
  let Px : Nat := 3480+7224*z
  let Py : Nat := 3439+7140*z
  let Qx : Nat := 3457+7182*z
  let Qy : Nat := 3447+7161*z
  let R0x : Nat := 3450+28686*u
  let R0y : Nat := 3447+28665*u
  let R1x : Nat := 27019216+29363712*s
  let R1y : Nat := 6752330+7338240*s
  let R2x : Nat := 33771544+36701952*s
  let R2y : Nat := 3376164+3669120*s
  let R3x : Nat := 37147706+40371072*s
  let R3y : Nat := 1688081+1834560*s
  let Vx : Nat := 19417891+21102816*s
  let Vy : Nat := 10552985+11468688*s
  let Wx : Nat := 14985436+16285752*s
  let Wy : Nat := 12769209+13877220*s
  change ¬ BB6.Agent3.CReach Px Py
  intro hP
  have hPx : Px%2=0 := by dsimp [Px]; omega
  have hPy : Py%2=1 := by dsimp [Py]; omega
  have hPy5 : 5≤Py := by dsimp [Py]; omega
  have hPmod : (Px+Py+1)%16=8 := by dsimp [Px,Py,z,u]; omega
  have hPsize : 23≤Px+Py := by dsimp [Px,Py]; omega
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      Px Py (by dsimp [Px]; omega) hP
  have hPparent := (BB6.Agent3.odd_seven_parent_iff a k Px Py
    hPx hPy hPy5 hPmod hPsize).mp hstep
  rcases hPparent with ⟨hsumP,hcostP⟩
  have haQ : a=Qx := by dsimp [Px,Py,Qx,z,u] at hsumP ⊢; omega
  have hkQ : k=Qy := by dsimp [Px,Py,Qy,z,u] at hcostP ⊢; omega
  have hQ : BB6.Agent3.CReach Qx Qy := by
    rw [haQ,hkQ] at hprev
    exact hprev
  have hQx : Qx%2=1 := by dsimp [Qx]; omega
  have hQy : Qy%2=1 := by dsimp [Qy]; omega
  have hQy5 : 5≤Qy := by dsimp [Qy]; omega
  have hQsum : (Qx+Qy)%8=4 := by dsimp [Qx,Qy,z,u]; omega
  obtain ⟨a2,k2,hprev2,hstep2⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      Qx Qy (by dsimp [Qx]; omega) hQ
  have hQparent := (BB6.Agent3.oddodd_parent_iff a2 k2 Qx Qy
    hQx hQy hQy5 hQsum).mp hstep2
  rcases hQparent with ⟨hsumQ,hcostQ⟩
  have haR : a2=R0x := by dsimp [Qx,Qy,R0x,z,u] at hsumQ ⊢; omega
  have hkR : k2=R0y := by dsimp [Qx,Qy,R0y,z,u] at hcostQ ⊢; omega
  have hR0 : BB6.Agent3.CReach R0x R0y := by
    rw [haR,hkR] at hprev2
    exact hprev2
  have hR0y6 : 6≤R0y := by dsimp [R0y,u]; omega
  have hR0yeven : R0y%2=0 := by dsimp [R0y,u]; omega
  have hR0sum : (R0x+R0y)%8=2 := by dsimp [R0x,R0y,u]; omega
  have hR1 : BB6.Agent3.CReach R1x R1y := by
    have hp := (BB6.Agent15.blank_reach_iff_even_right
      R0x R0y hR0y6 hR0yeven (by omega) (by omega)).mp hR0
    have hx : R0x+R0y-2=R1x := by dsimp [R0x,R0y,R1x,u]; omega
    have hy : (R0y-2)/2=R1y := by dsimp [R0y,R1y,u]; omega
    simpa only [hx,hy] using hp
  have hR1y6 : 6≤R1y := by dsimp [R1y]; omega
  have hR1yeven : R1y%2=0 := by dsimp [R1y]; omega
  have hR1sum : (R1x+R1y)%8=2 := by dsimp [R1x,R1y]; omega
  have hR2 : BB6.Agent3.CReach R2x R2y := by
    have hp := (BB6.Agent15.blank_reach_iff_even_right
      R1x R1y hR1y6 hR1yeven (by omega) (by omega)).mp hR1
    have hx : R1x+R1y-2=R2x := by dsimp [R1x,R1y,R2x]; omega
    have hy : (R1y-2)/2=R2y := by dsimp [R1y,R2y]; omega
    simpa only [hx,hy] using hp
  have hR2y6 : 6≤R2y := by dsimp [R2y]; omega
  have hR2yeven : R2y%2=0 := by dsimp [R2y]; omega
  have hR2sum : (R2x+R2y)%8=4 := by dsimp [R2x,R2y]; omega
  have hR3 : BB6.Agent3.CReach R3x R3y := by
    have hp := (BB6.Agent15.blank_reach_iff_even_right
      R2x R2y hR2y6 hR2yeven (by omega) (by omega)).mp hR2
    have hx : R2x+R2y-2=R3x := by dsimp [R2x,R2y,R3x]; omega
    have hy : (R2y-2)/2=R3y := by dsimp [R2y,R3y]; omega
    simpa only [hx,hy] using hp
  have hR3y5 : 5≤R3y := by dsimp [R3y]; omega
  have hR3yodd : R3y%2=1 := by dsimp [R3y]; omega
  have hR3sum : (R3x+R3y)%8=3 := by dsimp [R3x,R3y]; omega
  obtain ⟨a3,k3,hprev3,hstep3⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      R3x R3y (by dsimp [R3x]; omega) hR3
  have hR3parent :=
    (BB6.Agent46SourceInverse.section_evenodd_sum3_inverse
      a3 k3 R3x R3y hR3y5 hR3yodd hR3sum hstep3)
  rcases hR3parent with ⟨hparentX,hparentY⟩
  have haV : a3=Vx := by dsimp [R3x,R3y,Vx] at hparentX ⊢; omega
  have hkV : k3=Vy := by dsimp [R3x,R3y,Vy] at hparentY ⊢; omega
  have hV : BB6.Agent3.CReach Vx Vy := by
    rw [haV,hkV] at hprev3
    exact hprev3
  have hVx : Vx%2=1 := by dsimp [Vx]; omega
  have hVy : Vy%2=1 := by dsimp [Vy]; omega
  have hVy5 : 5≤Vy := by dsimp [Vy]; omega
  have hVsum4 : (Vx+Vy)%4=0 := by dsimp [Vx,Vy]; omega
  have hVnot16 : (Vx+Vy)%16≠0 := by dsimp [Vx,Vy]; omega
  have hVsize : 24≤Vx+Vy := by dsimp [Vx,Vy]; omega
  obtain ⟨a4,k4,hprev4,hstep4⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      Vx Vy (by dsimp [Vx]; omega) hV
  have hVparent := (BB6.Agent3.oddodd_lowval_parent_iff a4 k4 Vx Vy
    hVx hVy hVy5 hVsum4 hVnot16 hVsize).mp hstep4
  rcases hVparent with ⟨hsumV,hcostV⟩
  have haW : a4=Wx := by dsimp [Vx,Vy,Wx] at hsumV ⊢; omega
  have hkW : k4=Wy := by dsimp [Vx,Vy,Wy] at hcostV ⊢; omega
  have hW : BB6.Agent3.CReach Wx Wy := by
    rw [haW,hkW] at hprev4
    exact hprev4
  have hWx : 5<Wx := by dsimp [Wx]; omega
  have hWy5 : 5≤Wy := by dsimp [Wy]; omega
  have hWyodd : Wy%2=1 := by dsimp [Wy]; omega
  have hWsum : (Wx+Wy)%4=1 := by dsimp [Wx,Wy]; omega
  exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    Wx Wy hWx hWy5 hWyodd hWsum hW

#print axioms w7_q0_target_unreachable_z1884mod2048
end BB6.Agent15U5W7R21
