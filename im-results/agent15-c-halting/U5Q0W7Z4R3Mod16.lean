import U5Q0W7ParentFan
import EvenRightUnique
import Lean.Elab.Tactic.Omega

/-!
A second exact-source sublift in the z divisible-by-four sector.
For z=60+256t, the forced P -> Q -> R0 chain is followed by four
unique even-right inverses, ending at an odd-right sum-one state.
This is an intermediate source-composition draft; local Lean preflight
and original-source CI are still required.
-/

namespace BB6.Agent15U5W7Z4R3
open BB6.Agent46

/-- The z=60 (mod 256) member of the z=0 (mod 4) sector is blank-unreachable. -/
theorem w7_q0_target_unreachable_z60mod256 (t : Nat) :
    ¬ BB6.Agent3.CReach (436920+1849344*t) (431839+1827840*t) := by
  let u : Nat := 15+64*t
  let z : Nat := 4*u
  let Px : Nat := 3480+7224*z
  let Py : Nat := 3439+7140*z
  let Qx : Nat := 3457+7182*z
  let Qy : Nat := 3447+7161*z
  let R0x : Nat := 3450+28686*u
  let R0y : Nat := 3447+28665*u
  let R1x : Nat := 867160+3670464*t
  let R1y : Nat := 216710+917280*t
  let R2x : Nat := 1083868+4587744*t
  let R2y : Nat := 108354+458640*t
  let R3x : Nat := 1192220+5046384*t
  let R3y : Nat := 54176+229320*t
  let R4x : Nat := 1246394+5275704*t
  let R4y : Nat := 27087+114660*t
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
  have hR1sum : (R1x+R1y)%8=6 := by dsimp [R1x,R1y]; omega
  have hR2 : BB6.Agent3.CReach R2x R2y := by
    have hp := (BB6.Agent15.blank_reach_iff_even_right
      R1x R1y hR1y6 hR1yeven (by omega) (by omega)).mp hR1
    have hx : R1x+R1y-2=R2x := by dsimp [R1x,R1y,R2x]; omega
    have hy : (R1y-2)/2=R2y := by dsimp [R1y,R2y]; omega
    simpa only [hx,hy] using hp
  have hR2y6 : 6≤R2y := by dsimp [R2y]; omega
  have hR2yeven : R2y%2=0 := by dsimp [R2y]; omega
  have hR2sum : (R2x+R2y)%8=6 := by dsimp [R2x,R2y]; omega
  have hR3 : BB6.Agent3.CReach R3x R3y := by
    have hp := (BB6.Agent15.blank_reach_iff_even_right
      R2x R2y hR2y6 hR2yeven (by omega) (by omega)).mp hR2
    have hx : R2x+R2y-2=R3x := by dsimp [R2x,R2y,R3x]; omega
    have hy : (R2y-2)/2=R3y := by dsimp [R2y,R3y]; omega
    simpa only [hx,hy] using hp
  have hR3y6 : 6≤R3y := by dsimp [R3y]; omega
  have hR3yeven : R3y%2=0 := by dsimp [R3y]; omega
  have hR3sum : (R3x+R3y)%8=4 := by dsimp [R3x,R3y]; omega
  have hR4 : BB6.Agent3.CReach R4x R4y := by
    have hp := (BB6.Agent15.blank_reach_iff_even_right
      R3x R3y hR3y6 hR3yeven (by omega) (by omega)).mp hR3
    have hx : R3x+R3y-2=R4x := by dsimp [R3x,R3y,R4x]; omega
    have hy : (R3y-2)/2=R4y := by dsimp [R3y,R4y]; omega
    simpa only [hx,hy] using hp
  have hR4x : 5<R4x := by dsimp [R4x]; omega
  have hR4y5 : 5≤R4y := by dsimp [R4y]; omega
  have hR4yodd : R4y%2=1 := by dsimp [R4y]; omega
  have hR4sum : (R4x+R4y)%4=1 := by dsimp [R4x,R4y]; omega
  exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    R4x R4y hR4x hR4y5 hR4yodd hR4sum hR4

#print axioms w7_q0_target_unreachable_z60mod256
end BB6.Agent15U5W7Z4R3
