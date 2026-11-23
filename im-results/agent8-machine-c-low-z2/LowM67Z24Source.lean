import LowM67Z7Source
import Lean.Elab.Tactic.Omega

/-!
# Third source-authentic Machine C low-stop exclusion: z ≡ 24 mod 32

A uniform original-source inverse path E-B-B-B has no exception or
unbounded bounce branches in this infinite cylinder. The final forced
predecessor violates the original section's odd-image invariant.
-/

namespace BB6.Agent8CLowZ24
open BB6.Agent46 BB6.Agent3

/-- For every u congruent 47 modulo 64, the exact four-source inverse
from (180u+28,166u+25) ends at an odd-right, sum-2-mod-4
forbidden state of the genuine blank-root orbit. -/
theorem rectangle_u47_mod64_unreachable
    (u : Nat) (hu : u%64=47) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  let t := u/64
  have hU : u=64*t+47 := by
    have hh := Nat.mod_add_div u 64
    dsimp [t]
    omega
  intro hr
  have hfirst := (BB6.Agent3.evenodd_four_blank_reach_iff
      (180*u+28) (166*u+25)
      (by omega) (by omega) (by omega)
      (by rw [hU]; omega)).mp hr
  rw [hU] at hfirst
  have h1 : BB6.Agent3.CReach (11072*t+8155) (10848*t+7990) := by
    simpa only [BB6.Agent3.CReach,
      show ((180*(64*t+47)+28)+(166*(64*t+47)+25)-5)/2 =
        11072*t+8155 by omega,
      show ((180*(64*t+47)+28)+3*(166*(64*t+47)+25)-9)/4 =
        10848*t+7990 by omega] using hfirst
  have hsecond := (BB6.Agent46.six_even_right_blank_reach_iff
      (11072*t+8155) (10848*t+7990)
      (by omega) (by omega) (by omega) (by omega)).mp h1
  have h2 : BB6.Agent3.CReach (21920*t+16143) (5424*t+3994) := by
    simpa only [BB6.Agent3.CReach,
      show (11072*t+8155)+(10848*t+7990)-2 =
        21920*t+16143 by omega,
      show ((10848*t+7990)-2)/2 = 5424*t+3994 by omega] using hsecond
  have hthird := (BB6.Agent46.six_even_right_blank_reach_iff
      (21920*t+16143) (5424*t+3994)
      (by omega) (by omega) (by omega) (by omega)).mp h2
  have h3 : BB6.Agent3.CReach (27344*t+20135) (2712*t+1996) := by
    simpa only [BB6.Agent3.CReach,
      show (21920*t+16143)+(5424*t+3994)-2 =
        27344*t+20135 by omega,
      show ((5424*t+3994)-2)/2 = 2712*t+1996 by omega] using hthird
  have hfourth := (BB6.Agent46.six_even_right_blank_reach_iff
      (27344*t+20135) (2712*t+1996)
      (by omega) (by omega) (by omega) (by omega)).mp h3
  have h4 : BB6.Agent3.CReach (30056*t+22129) (1356*t+997) := by
    simpa only [BB6.Agent3.CReach,
      show (27344*t+20135)+(2712*t+1996)-2 =
        30056*t+22129 by omega,
      show ((2712*t+1996)-2)/2 = 1356*t+997 by omega] using hfourth
  exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
    (by omega) (by omega) (Or.inr (by omega))) h4

/-- For m=512z+67, no actual low stopping target exists in
z ≡ 24 (mod 32), an additional 128 disjoint residue classes mod 4096. -/
theorem low_stop_m67_z24_mod32_unreachable
    (z m k : Nat) (hm : m=512*z+67) (hz : z%32=24)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 16384 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^14 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^14=16384 by decide] using h
  have hpmod : (2^(2*m+3))%16384=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hzEq : z=32*(z/32)+24 := by
    have hh := Nat.mod_add_div z 32
    omega
  have hkmod : k%16384=12083 := by
    have hs : (k+3*m+4)%16384=0 := by
      rw [hstop]
      exact hpmod
    rw [hm,hzEq] at hs
    omega
  let u := 64*(k/16384)+47
  have hu : u%64=47 := by dsimp [u]; omega
  have hk : k=256*u+51 := by
    have hh := Nat.mod_add_div k 16384
    rw [hkmod] at hh
    dsimp [u]
    omega
  rw [hk]
  intro hr
  exact (rectangle_u47_mod64_unreachable u hu)
    (BB6.Agent13One307.four_step_to_rectangle u hr)

#print axioms rectangle_u47_mod64_unreachable
#print axioms low_stop_m67_z24_mod32_unreachable
end BB6.Agent8CLowZ24
