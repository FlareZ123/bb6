import U5Q0W7ParentFan
import EvenRightUnique
import Lean.Elab.Tactic.Omega

/-!
A further exact-source sublift in the still-open z divisible-by-four
sector. For z=12+64v, the forced P -> Q -> R ancestry is followed by
two unique even-right inverses, ending in an odd-right sum-one state.
This is an intermediate source-composition draft; local Lean preflight
and original-source CI are still required.
-/

namespace BB6.Agent15U5W7Z4
open BB6.Agent46

/-- The z=12 (mod 64) member of the z=0 (mod 4) sector is blank-unreachable.
    The proof uses only exact original-source parent theorems and the
    source-certified even-right reachability equivalence. -/
theorem w7_q0_target_unreachable_z12mod64 (v : Nat) :
    ¬ BB6.Agent3.CReach (90168+462336*v) (89119+456960*v) := by
  let u : Nat := 3+16*v
  let z : Nat := 4*u
  let Px : Nat := 3480+7224*z
  let Py : Nat := 3439+7140*z
  let Qx : Nat := 3457+7182*z
  let Qy : Nat := 3447+7161*z
  let R0x : Nat := 3450+28686*u
  let R0y : Nat := 3447+28665*u
  let R1x : Nat := 178948+917616*v
  let R1y : Nat := 44720+229320*v
  let R2x : Nat := 223666+1146936*v
  let R2y : Nat := 22359+114660*v
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
  have hR0sum : (R0x+R0y)%8=6 := by dsimp [R0x,R0y,u]; omega
  have hR1 : BB6.Agent3.CReach R1x R1y := by
    have hp := (BB6.Agent15.blank_reach_iff_even_right
      R0x R0y hR0y6 hR0yeven (by omega) (by omega)).mp hR0
    have hx : R0x+R0y-2=R1x := by dsimp [R0x,R0y,R1x,u]; omega
    have hy : (R0y-2)/2=R1y := by dsimp [R0y,R1y,u]; omega
    simpa only [hx,hy] using hp
  have hR1y6 : 6≤R1y := by dsimp [R1y]; omega
  have hR1yeven : R1y%2=0 := by dsimp [R1y]; omega
  have hR1sum : (R1x+R1y)%8=4 := by dsimp [R1x,R1y]; omega
  have hR2 : BB6.Agent3.CReach R2x R2y := by
    have hp := (BB6.Agent15.blank_reach_iff_even_right
      R1x R1y hR1y6 hR1yeven (by omega) (by omega)).mp hR1
    have hx : R1x+R1y-2=R2x := by dsimp [R1x,R1y,R2x]; omega
    have hy : (R1y-2)/2=R2y := by dsimp [R1y,R2y]; omega
    simpa only [hx,hy] using hp
  have hR2x : 5<R2x := by dsimp [R2x]; omega
  have hR2y5 : 5≤R2y := by dsimp [R2y]; omega
  have hR2yodd : R2y%2=1 := by dsimp [R2y]; omega
  have hR2sum : (R2x+R2y)%4=1 := by dsimp [R2x,R2y]; omega
  exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    R2x R2y hR2x hR2y5 hR2yodd hR2sum hR2

#print axioms w7_q0_target_unreachable_z12mod64
end BB6.Agent15U5W7Z4
