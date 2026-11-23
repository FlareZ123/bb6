import LowM67Z44Source
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

/-!
A second disjoint source-authentic low-stop cylinder:
m=512z+67 with z ≡16 mod128, equivalent to u≡159 mod256.

The exact original-source forced inverse chain from R_u is F-A-A-A-A-B,
terminating in an odd-right image with sum 2 mod4. No finite-tape
simulation, bounded halting time or synthetic next-step relation.
-/

namespace BB6.Agent13LowZ16
open BB6.Agent3 BB6.Agent46

/-- The affine rectangle x=180u+28, y=166u+25 at u=159 mod256
    is absent from the genuine original blank section orbit. -/
theorem rectangle_u159_mod256_unreachable
    (u : Nat) (hu : u%256=159) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  let t := u/256
  have hU : u=256*t+159 := by
    have hh := Nat.mod_add_div u 256
    dsimp [t]
    omega
  intro hr
  have hfirst := (BB6.Agent3.evenodd_four_blank_reach_iff
      (180*u+28) (166*u+25)
      (by omega) (by omega) (by omega)
      (by rw [hU]; omega)).mp hr
  rw [hU] at hfirst
  have h1 : BB6.Agent3.CReach
      (44288*t+27531) (43392*t+26974) := by
    simpa only [BB6.Agent3.CReach,
      show ((180*(256*t+159)+28)+(166*(256*t+159)+25)-5)/2 =
        44288*t+27531 by omega,
      show ((180*(256*t+159)+28)+3*(166*(256*t+159)+25)-9)/4 =
        43392*t+26974 by omega] using hfirst
  have hsecond := (BB6.Agent15.blank_reach_iff_affine
      (44288*t+27531) (43392*t+26974)
      (by omega) (by omega) (by omega)).mp h1
  have h2 : BB6.Agent3.CReach (87680*t+54503) (21696*t+13486) := by
    simpa only [BB6.Agent3.CReach,
      show (44288*t+27531)+(43392*t+26974)-2 =
        87680*t+54503 by omega,
      show ((43392*t+26974)-2)/2 =21696*t+13486 by omega] using hsecond
  have hthird := (BB6.Agent15.blank_reach_iff_affine
      (87680*t+54503) (21696*t+13486)
      (by omega) (by omega) (by omega)).mp h2
  have h3 : BB6.Agent3.CReach (109376*t+67987) (10848*t+6742) := by
    simpa only [BB6.Agent3.CReach,
      show (87680*t+54503)+(21696*t+13486)-2 =
        109376*t+67987 by omega,
      show ((21696*t+13486)-2)/2 =10848*t+6742 by omega] using hthird
  have hfourth := (BB6.Agent15.blank_reach_iff_affine
      (109376*t+67987) (10848*t+6742)
      (by omega) (by omega) (by omega)).mp h3
  have h4 : BB6.Agent3.CReach (120224*t+74727) (5424*t+3370) := by
    simpa only [BB6.Agent3.CReach,
      show (109376*t+67987)+(10848*t+6742)-2 =
        120224*t+74727 by omega,
      show ((10848*t+6742)-2)/2 =5424*t+3370 by omega] using hfourth
  have hfifth := (BB6.Agent15.blank_reach_iff_affine
      (120224*t+74727) (5424*t+3370)
      (by omega) (by omega) (by omega)).mp h4
  have h5 : BB6.Agent3.CReach (125648*t+78095) (2712*t+1684) := by
    simpa only [BB6.Agent3.CReach,
      show (120224*t+74727)+(5424*t+3370)-2 =
        125648*t+78095 by omega,
      show ((5424*t+3370)-2)/2 =2712*t+1684 by omega] using hfifth
  have hsixth := (BB6.Agent46.six_even_right_blank_reach_iff
      (125648*t+78095) (2712*t+1684)
      (by omega) (by omega) (by omega) (by omega)).mp h5
  have h6 : BB6.Agent3.CReach (128360*t+79777) (1356*t+841) := by
    simpa only [BB6.Agent3.CReach,
      show (125648*t+78095)+(2712*t+1684)-2 =
        128360*t+79777 by omega,
      show ((2712*t+1684)-2)/2 =1356*t+841 by omega] using hsixth
  exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
    (by omega) (by omega) (Or.inr (by omega))) h6

/-- All genuine low stopping targets m=512z+67 with z=16 (mod128)
    are absent from the original blank section orbit, for all time. -/
theorem low_stop_m67_z16_mod128_unreachable
    (z m k : Nat) (hm : m=512*z+67) (hz : z%128=16)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 65536 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^16 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^16=65536 by decide] using h
  have hpmod : (2^(2*m+3))%65536=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hzEq : z=128*(z/128)+16 := by
    have hh := Nat.mod_add_div z 128
    omega
  have hkmod : k%65536=40755 := by
    have hs : (k+3*m+4)%65536=0 := by
      rw [hstop]
      exact hpmod
    rw [hm,hzEq] at hs
    omega
  let u := 256*(k/65536)+159
  have hu : u%256=159 := by dsimp [u]; omega
  have hk : k=256*u+51 := by
    have hh := Nat.mod_add_div k 65536
    rw [hkmod] at hh
    dsimp [u]
    omega
  rw [hk]
  intro hr
  exact (rectangle_u159_mod256_unreachable u hu)
    (BB6.Agent13One307.four_step_to_rectangle u hr)

#print axioms rectangle_u159_mod256_unreachable
#print axioms low_stop_m67_z16_mod128_unreachable
end BB6.Agent13LowZ16
