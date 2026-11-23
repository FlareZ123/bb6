import LowM67Z24Source
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

/-!
An additional all-time original Machine C low-stop exclusion:
z ≡ 44 mod64 in m=512z+67, disjoint from the earlier z≡2 mod8,
z≡7 mod16, z≡24 mod32 and Agent 13's 559-class sieve.

The exact source inverse word from R_u at u≡119 mod128 is
F-A-B-O, terminating in an odd-right sum-one-mod-four forbidden state.
No finite-time or quotient assumptions are involved.
-/

namespace BB6.Agent13LowZ44
open BB6.Agent3 BB6.Agent46

/-- An original-source all-time exclusion of every section state in this
    explicit affine ray. The four inverse steps use, respectively, the
    complete even/odd valuation-two source, affine right-even source,
    six-residue even-right source and odd/odd low-valuation source. -/
theorem rectangle_u119_mod128_unreachable
    (u : Nat) (hu : u%128=119) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  let t := u/128
  have hU : u=128*t+119 := by
    have hh := Nat.mod_add_div u 128
    dsimp [t]
    omega
  intro hr
  have hfirst := (BB6.Agent3.evenodd_four_blank_reach_iff
      (180*u+28) (166*u+25)
      (by omega) (by omega) (by omega)
      (by rw [hU]; omega)).mp hr
  rw [hU] at hfirst
  have h1 : BB6.Agent3.CReach
      (22144*t+20611) (21696*t+20194) := by
    simpa only [BB6.Agent3.CReach,
      show ((180*(128*t+119)+28)+(166*(128*t+119)+25)-5)/2 =
        22144*t+20611 by omega,
      show ((180*(128*t+119)+28)+3*(166*(128*t+119)+25)-9)/4 =
        21696*t+20194 by omega] using hfirst
  have hsecond := (BB6.Agent15.blank_reach_iff_affine
      (22144*t+20611) (21696*t+20194)
      (by omega) (by omega) (by omega)).mp h1
  have h2 : BB6.Agent3.CReach (43840*t+40803) (10848*t+10096) := by
    simpa only [BB6.Agent3.CReach,
      show (22144*t+20611)+(21696*t+20194)-2 =
        43840*t+40803 by omega,
      show ((21696*t+20194)-2)/2 =10848*t+10096 by omega] using hsecond
  have hthird := (BB6.Agent46.six_even_right_blank_reach_iff
      (43840*t+40803) (10848*t+10096)
      (by omega) (by omega) (by omega) (by omega)).mp h2
  have h3 : BB6.Agent3.CReach (54688*t+50897) (5424*t+5047) := by
    simpa only [BB6.Agent3.CReach,
      show (43840*t+40803)+(10848*t+10096)-2 =
        54688*t+50897 by omega,
      show ((10848*t+10096)-2)/2 = 5424*t+5047 by omega] using hthird
  have hfourth := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (54688*t+50897) (5424*t+5047)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).mp h3
  have h4 : BB6.Agent3.CReach (30056*t+27970) (17740*t+16507) := by
    simpa only [BB6.Agent3.CReach,
      show ((54688*t+50897)+(5424*t+5047)-4)/2 =
        30056*t+27970 by omega,
      show ((54688*t+50897)+3*(5424*t+5047)-10)/4 =
        17740*t+16507 by omega] using hfourth
  exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
    (by omega) (by omega) (Or.inl (by omega))) h4

/-- Entire necessary low-halting parameter progression:
    m=512z+67 and z=44 (mod64) is impossible from the genuine
    blank section orbit, with no restriction on z or halting time. -/
theorem low_stop_m67_z44_mod64_unreachable
    (z m k : Nat) (hm : m=512*z+67) (hz : z%64=44)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 32768 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^15 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^15=32768 by decide] using h
  have hpmod : (2^(2*m+3))%32768=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hzEq : z=64*(z/64)+44 := by
    have hh := Nat.mod_add_div z 64
    omega
  have hkmod : k%32768=30515 := by
    have hs : (k+3*m+4)%32768=0 := by
      rw [hstop]
      exact hpmod
    rw [hm,hzEq] at hs
    omega
  let u := 128*(k/32768)+119
  have hu : u%128=119 := by dsimp [u]; omega
  have hk : k=256*u+51 := by
    have hh := Nat.mod_add_div k 32768
    rw [hkmod] at hh
    dsimp [u]
    omega
  rw [hk]
  intro hr
  exact (rectangle_u119_mod128_unreachable u hu)
    (BB6.Agent13One307.four_step_to_rectangle u hr)

#print axioms rectangle_u119_mod128_unreachable
#print axioms low_stop_m67_z44_mod64_unreachable
end BB6.Agent13LowZ44
