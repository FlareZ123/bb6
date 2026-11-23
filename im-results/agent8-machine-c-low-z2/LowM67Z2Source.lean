import LowM67FiveD23Source
import Lean.Elab.Tactic.Omega

/-!
# Authentic Machine C low-stop family z ≡ 2 (mod 8)

New disjoint low-stop cylinder. The first unique predecessor of
(180u+28,166u+25), u ≡ 3 mod 16, is even-right and has a second unique
predecessor in the forbidden odd-image sum-2 residue.

This is an all-time source-reachability theorem, not a Machine C
nonhalting proof or a BB(6) maximality theorem.
-/

namespace BB6.Agent8CLowZ2

open BB6.Agent46 BB6.Agent3

/-- All authentic blank-root section paths avoid the complete affine
rectangle (180u+28,166u+25) for every u ≡ 3 (mod 16).
The first inverse uses the original even/odd valuation-two uniqueness
theorem; the second uses the original even-right uniqueness theorem. -/
theorem rectangle_u3_mod16_unreachable
    (u : Nat) (hu : u%16=3) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  let t := u/16
  have hU : u=16*t+3 := by
    have hh := Nat.mod_add_div u 16
    dsimp [t]
    omega
  intro hr
  have hfirst := (BB6.Agent3.evenodd_four_blank_reach_iff
      (180*u+28) (166*u+25)
      (by omega) (by omega) (by omega)
      (by rw [hU]; omega)).mp hr
  rw [hU] at hfirst
  have hpre : BB6.Agent3.CReach
      (2768*t+543) (2712*t+532) := by
    simpa only [BB6.Agent3.CReach,
      show ((180*(16*t+3)+28)+(166*(16*t+3)+25)-5)/2 =
        2768*t+543 by omega,
      show ((180*(16*t+3)+28)+3*(166*(16*t+3)+25)-9)/4 =
        2712*t+532 by omega] using hfirst
  have hsecond := (BB6.Agent46.six_even_right_blank_reach_iff
      (2768*t+543) (2712*t+532)
      (by omega) (by omega) (by omega) (by omega)).mp hpre
  have hbad : BB6.Agent3.CReach
      (5480*t+1073) (1356*t+265) := by
    simpa only [BB6.Agent3.CReach,
      show (2768*t+543)+(2712*t+532)-2 =
        5480*t+1073 by omega,
      show ((2712*t+532)-2)/2 = 1356*t+265 by omega] using hsecond
  exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
    (by omega) (by omega) (Or.inr (by omega))) hbad

/-- For m=512z+67, every actual low stop with z ≡ 2 (mod 8) would
force an excluded rectangle. This family is disjoint from all prior
559/4096 low-index residues (which were odd). -/
theorem low_stop_m67_z2_mod8_unreachable
    (z m k : Nat) (hm : m=512*z+67) (hz : z%8=2)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 4096 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^12 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^12=4096 by decide] using h
  have hpmod : (2^(2*m+3))%4096=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hzEq : z=8*(z/8)+2 := by
    have hh := Nat.mod_add_div z 8
    omega
  have hkmod : k%4096=819 := by
    have hs : (k+3*m+4)%4096=0 := by
      rw [hstop]
      exact hpmod
    rw [hm,hzEq] at hs
    omega
  let u := 16*(k/4096)+3
  have hu : u%16=3 := by dsimp [u]; omega
  have hk : k=256*u+51 := by
    have hh := Nat.mod_add_div k 4096
    rw [hkmod] at hh
    dsimp [u]
    omega
  rw [hk]
  intro hr
  exact (rectangle_u3_mod16_unreachable u hu)
    (BB6.Agent13One307.four_step_to_rectangle u hr)

#print axioms rectangle_u3_mod16_unreachable
#print axioms low_stop_m67_z2_mod8_unreachable

end BB6.Agent8CLowZ2
