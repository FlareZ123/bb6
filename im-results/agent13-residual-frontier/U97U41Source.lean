import One307Source
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13U97U41
open BB6.Agent46 BB6.Agent3

/-- For u=97 (mod128), the two parent sources are respectively a direct
    forbidden odd-image cell and one exact odd/odd low-gate predecessor
    whose image is forbidden. -/
theorem source_rectangle_u97_mod128 (u : Nat) (hu : u%128=97) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  let t := u/128
  have hU : u=128*t+97 := by
    have h := Nat.mod_add_div u 128
    dsimp [t]
    omega
  have hL0 : BB6.Agent13TwoParent.parentLeft
      (180*u+28) (166*u+25) 0 =22144*t+16805 := by
    simp [BB6.Agent13TwoParent.parentLeft,hU]
    omega
  have hR0 : BB6.Agent13TwoParent.parentRight
      (180*u+28) (166*u+25) 0 =21696*t+16465 := by
    simp [BB6.Agent13TwoParent.parentRight,
      BB6.Agent13TwoParent.parentLeft,hU]
    omega
  have hL2 : BB6.Agent13TwoParent.parentLeft
      (180*u+28) (166*u+25) 2 =5536*t+4199 := by
    simp [BB6.Agent13TwoParent.parentLeft,hU]
    omega
  have hR2 : BB6.Agent13TwoParent.parentRight
      (180*u+28) (166*u+25) 2 =30000*t+22765 := by
    simp [BB6.Agent13TwoParent.parentRight,
      BB6.Agent13TwoParent.parentLeft,hU]
    omega
  have h0 : ¬ BB6.Agent3.CReach
      (BB6.Agent13TwoParent.parentLeft (180*u+28) (166*u+25) 0)
      (BB6.Agent13TwoParent.parentRight (180*u+28) (166*u+25) 0) := by
    rw [hL0,hR0]
    exact BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))
  have h2 : ¬ BB6.Agent3.CReach
      (BB6.Agent13TwoParent.parentLeft (180*u+28) (166*u+25) 2)
      (BB6.Agent13TwoParent.parentRight (180*u+28) (166*u+25) 2) := by
    rw [hL2,hR2]
    intro hp
    have hh := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (5536*t+4199) (30000*t+22765)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).mp hp
    have ht : BB6.Agent3.CReach
        (17768*t+13480) (23884*t+18121) := by
      simpa only [BB6.Agent3.CReach,
        show ((5536*t+4199)+(30000*t+22765)-4)/2=
          17768*t+13480 by omega,
        show ((5536*t+4199)+3*(30000*t+22765)-10)/4=
          23884*t+18121 by omega] using hh
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inl (by omega))) ht
  exact BB6.Agent13TwoParent.two_parent_nonreach
    (180*u+28) (166*u+25)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) h0 h2

/-- For u=41 (mod64), the depth-two parent has one exact even affine
    predecessor with odd right counter and image sum two modulo four. -/
theorem source_rectangle_u41_mod64 (u : Nat) (hu : u%64=41) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  let t := u/64
  have hU : u=64*t+41 := by
    have h := Nat.mod_add_div u 64
    dsimp [t]
    omega
  have hL0 : BB6.Agent13TwoParent.parentLeft
      (180*u+28) (166*u+25) 0 =11072*t+7117 := by
    simp [BB6.Agent13TwoParent.parentLeft,hU]
    omega
  have hR0 : BB6.Agent13TwoParent.parentRight
      (180*u+28) (166*u+25) 0 =10848*t+6973 := by
    simp [BB6.Agent13TwoParent.parentRight,
      BB6.Agent13TwoParent.parentLeft,hU]
    omega
  have hL2 : BB6.Agent13TwoParent.parentLeft
      (180*u+28) (166*u+25) 2 =2768*t+1777 := by
    simp [BB6.Agent13TwoParent.parentLeft,hU]
    omega
  have hR2 : BB6.Agent13TwoParent.parentRight
      (180*u+28) (166*u+25) 2 =15000*t+9640 := by
    simp [BB6.Agent13TwoParent.parentRight,
      BB6.Agent13TwoParent.parentLeft,hU]
    omega
  have h0 : ¬ BB6.Agent3.CReach
      (BB6.Agent13TwoParent.parentLeft (180*u+28) (166*u+25) 0)
      (BB6.Agent13TwoParent.parentRight (180*u+28) (166*u+25) 0) := by
    rw [hL0,hR0]
    exact BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))
  have h2 : ¬ BB6.Agent3.CReach
      (BB6.Agent13TwoParent.parentLeft (180*u+28) (166*u+25) 2)
      (BB6.Agent13TwoParent.parentRight (180*u+28) (166*u+25) 2) := by
    rw [hL2,hR2]
    intro hp
    have hh := (BB6.Agent15.blank_reach_iff_affine
      (2768*t+1777) (15000*t+9640)
      (by omega) (by omega) (by omega)).mp hp
    have ht : BB6.Agent3.CReach
        (17768*t+11415) (7500*t+4819) := by
      simpa only [BB6.Agent3.CReach,
        show ((2768*t+1777)+(15000*t+9640)-2)=
          17768*t+11415 by omega,
        show ((15000*t+9640)-2)/2=
          7500*t+4819 by omega] using hh
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))) ht
  exact BB6.Agent13TwoParent.two_parent_nonreach
    (180*u+28) (166*u+25)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) h0 h2

theorem low_stop_m67_z5_mod64_unreachable
    (z m k : Nat) (hm : m=512*z+67) (hz : z%64=5)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 32768 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^15 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^15=32768 by decide] using h
  have hpmod : (2^(2*m+3))%32768=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hkmod : k%32768=24883 := by
    have hs : (k+3*m+4)%32768=0 := by
      rw [hstop]
      exact hpmod
    rw [hm] at hs
    omega
  let u := 128*(k/32768)+97
  have hu : u%128=97 := by dsimp [u]; omega
  have hk : k=256*u+51 := by
    have hdecomp := Nat.mod_add_div k 32768
    rw [hkmod] at hdecomp
    dsimp [u]
    omega
  rw [hk]
  intro hr
  exact (source_rectangle_u97_mod128 u hu)
    (BB6.Agent13One307.four_step_to_rectangle u hr)

theorem low_stop_m67_z25_mod32_unreachable
    (z m k : Nat) (hm : m=512*z+67) (hz : z%32=25)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 16384 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^14 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^14=16384 by decide] using h
  have hpmod : (2^(2*m+3))%16384=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hkmod : k%16384=10547 := by
    have hs : (k+3*m+4)%16384=0 := by
      rw [hstop]
      exact hpmod
    rw [hm] at hs
    omega
  let u := 64*(k/16384)+41
  have hu : u%64=41 := by dsimp [u]; omega
  have hk : k=256*u+51 := by
    have hdecomp := Nat.mod_add_div k 16384
    rw [hkmod] at hdecomp
    dsimp [u]
    omega
  rw [hk]
  intro hr
  exact (source_rectangle_u41_mod64 u hu)
    (BB6.Agent13One307.four_step_to_rectangle u hr)

#print axioms low_stop_m67_z5_mod64_unreachable
#print axioms low_stop_m67_z25_mod32_unreachable
end BB6.Agent13U97U41
