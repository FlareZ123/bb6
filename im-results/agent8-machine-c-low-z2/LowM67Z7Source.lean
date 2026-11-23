import LowM67Z2Source
import Lean.Elab.Tactic.Omega

/-!
# A second disjoint Machine C low-stop source exclusion: z ≡ 7 mod 16

Original-section inverse path from the genuine blank root:
even/odd valuation-three -> odd/odd low valuation -> odd-image contradiction.
Unlike bounded simulation or quotient pruning, the theorems apply at every
section time and for all natural parameters in the full infinite cylinder.
-/

namespace BB6.Agent8CLowZ7

open BB6.Agent46 BB6.Agent3

/-- For every u congruent 21 modulo 32, the source-exact two-predecessor
path from (180u+28,166u+25) terminates in an odd-right target whose
coordinate sum is 1 modulo 4, which no genuine blank orbit can reach. -/
theorem rectangle_u21_mod32_unreachable
    (u : Nat) (hu : u%32=21) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  let t := u/32
  have hU : u=32*t+21 := by
    have hh := Nat.mod_add_div u 32
    dsimp [t]
    omega
  intro hr
  have hfirst := (BB6.Agent3.odd_seven_blank_reach_iff
      (180*u+28) (166*u+25)
      (by omega) (by omega) (by omega)
      (by rw [hU]; omega) (by omega)).mp hr
  rw [hU] at hfirst
  have hpre : BB6.Agent3.CReach
      (5536*t+3657) (5424*t+3583) := by
    simpa only [BB6.Agent3.CReach,
      show ((180*(32*t+21)+28)+(166*(32*t+21)+25)-5)/2 =
        5536*t+3657 by omega,
      show ((180*(32*t+21)+28)+3*(166*(32*t+21)+25)-9)/4 =
        5424*t+3583 by omega] using hfirst
  have hsecond := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (5536*t+3657) (5424*t+3583)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).mp hpre
  have hbad : BB6.Agent3.CReach
      (5480*t+3618) (5452*t+3599) := by
    simpa only [BB6.Agent3.CReach,
      show ((5536*t+3657)+(5424*t+3583)-4)/2 =
        5480*t+3618 by omega,
      show ((5536*t+3657)+3*(5424*t+3583)-10)/4 =
        5452*t+3599 by omega] using hsecond
  exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
    (by omega) (by omega) (Or.inl (by omega))) hbad

/-- Additional all-time original-source low-stop exclusion for
m=512z+67 and z ≡ 7 (mod 16), disjoint from the previously proved
odd-index 559 classes and the new even-index z ≡ 2 (mod 8) class. -/
theorem low_stop_m67_z7_mod16_unreachable
    (z m k : Nat) (hm : m=512*z+67) (hz : z%16=7)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 8192 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^13 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^13=8192 by decide] using h
  have hpmod : (2^(2*m+3))%8192=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hzEq : z=16*(z/16)+7 := by
    have hh := Nat.mod_add_div z 16
    omega
  have hkmod : k%8192=5427 := by
    have hs : (k+3*m+4)%8192=0 := by
      rw [hstop]
      exact hpmod
    rw [hm,hzEq] at hs
    omega
  let u := 32*(k/8192)+21
  have hu : u%32=21 := by dsimp [u]; omega
  have hk : k=256*u+51 := by
    have hh := Nat.mod_add_div k 8192
    rw [hkmod] at hh
    dsimp [u]
    omega
  rw [hk]
  intro hr
  exact (rectangle_u21_mod32_unreachable u hu)
    (BB6.Agent13One307.four_step_to_rectangle u hr)

#print axioms rectangle_u21_mod32_unreachable
#print axioms low_stop_m67_z7_mod16_unreachable

end BB6.Agent8CLowZ7
