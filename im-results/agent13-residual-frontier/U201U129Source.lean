import One307Source
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13U201U129
open BB6.Agent46 BB6.Agent3

/-- Source-only forbidden rectangle for u=201 modulo256:
    depth zero is an odd forbidden image, depth two is forced by A,O
    into an odd forbidden image. -/
theorem source_rectangle_u201_mod256 (u : Nat) (hu : u%256=201) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  let t := u/256
  have hU : u=256*t+201 := by
    have h := Nat.mod_add_div u 256
    dsimp [t]
    omega
  have hL0 : BB6.Agent13TwoParent.parentLeft
      (180*u+28) (166*u+25) 0 =44288*t+34797 := by
    simp [BB6.Agent13TwoParent.parentLeft,hU]
    omega
  have hR0 : BB6.Agent13TwoParent.parentRight
      (180*u+28) (166*u+25) 0 =43392*t+34093 := by
    simp [BB6.Agent13TwoParent.parentRight,
      BB6.Agent13TwoParent.parentLeft,hU]
    omega
  have hL2 : BB6.Agent13TwoParent.parentLeft
      (180*u+28) (166*u+25) 2 =11072*t+8697 := by
    simp [BB6.Agent13TwoParent.parentLeft,hU]
    omega
  have hR2 : BB6.Agent13TwoParent.parentRight
      (180*u+28) (166*u+25) 2 =60000*t+47140 := by
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
    have hA := (BB6.Agent15.blank_reach_iff_affine
      (11072*t+8697) (60000*t+47140)
      (by omega) (by omega) (by omega)).mp hp
    have htA : BB6.Agent3.CReach
        (71072*t+55835) (30000*t+23569) := by
      simpa only [BB6.Agent3.CReach,
        show (11072*t+8697)+(60000*t+47140)-2=
          71072*t+55835 by omega,
        show ((60000*t+47140)-2)/2=
          30000*t+23569 by omega] using hA
    have hO := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (71072*t+55835) (30000*t+23569)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).mp htA
    have htO : BB6.Agent3.CReach
        (50536*t+39700) (40268*t+31633) := by
      simpa only [BB6.Agent3.CReach,
        show ((71072*t+55835)+(30000*t+23569)-4)/2=
          50536*t+39700 by omega,
        show ((71072*t+55835)+3*(30000*t+23569)-10)/4=
          40268*t+31633 by omega] using hO
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inl (by omega))) htO
  exact BB6.Agent13TwoParent.two_parent_nonreach
    (180*u+28) (166*u+25)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) h0 h2

/-- Source-only forbidden rectangle for u=129 modulo256:
    depth zero has forbidden odd image, depth two has source-exact
    O,B predecessors ending in a forbidden odd image. -/
theorem source_rectangle_u129_mod256 (u : Nat) (hu : u%256=129) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  let t := u/256
  have hU : u=256*t+129 := by
    have h := Nat.mod_add_div u 256
    dsimp [t]
    omega
  have hL0 : BB6.Agent13TwoParent.parentLeft
      (180*u+28) (166*u+25) 0 =44288*t+22341 := by
    simp [BB6.Agent13TwoParent.parentLeft,hU]
    omega
  have hR0 : BB6.Agent13TwoParent.parentRight
      (180*u+28) (166*u+25) 0 =43392*t+21889 := by
    simp [BB6.Agent13TwoParent.parentRight,
      BB6.Agent13TwoParent.parentLeft,hU]
    omega
  have hL2 : BB6.Agent13TwoParent.parentLeft
      (180*u+28) (166*u+25) 2 =11072*t+5583 := by
    simp [BB6.Agent13TwoParent.parentLeft,hU]
    omega
  have hR2 : BB6.Agent13TwoParent.parentRight
      (180*u+28) (166*u+25) 2 =60000*t+30265 := by
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
    have hO := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (11072*t+5583) (60000*t+30265)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).mp hp
    have htO : BB6.Agent3.CReach
        (35536*t+17922) (47768*t+24092) := by
      simpa only [BB6.Agent3.CReach,
        show ((11072*t+5583)+(60000*t+30265)-4)/2=
          35536*t+17922 by omega,
        show ((11072*t+5583)+3*(60000*t+30265)-10)/4=
          47768*t+24092 by omega] using hO
    have hB := (BB6.Agent46.six_even_right_blank_reach_iff
      (35536*t+17922) (47768*t+24092)
      (by omega) (by omega) (by omega) (by omega)).mp htO
    have htB : BB6.Agent3.CReach
        (83304*t+42012) (23884*t+12045) := by
      simpa only [BB6.Agent3.CReach,
        show (35536*t+17922)+(47768*t+24092)-2=
          83304*t+42012 by omega,
        show ((47768*t+24092)-2)/2=
          23884*t+12045 by omega] using hB
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inl (by omega))) htB
  exact BB6.Agent13TwoParent.two_parent_nonreach
    (180*u+28) (166*u+25)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) h0 h2

theorem low_stop_m67_z9_mod128_unreachable
    (z m k : Nat) (hm : m=512*z+67) (hz : z%128=9)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 65536 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^16 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^16=65536 by decide] using h
  have hpmod : (2^(2*m+3))%65536=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hkmod : k%65536=51507 := by
    have hs : (k+3*m+4)%65536=0 := by
      rw [hstop]
      exact hpmod
    rw [hm] at hs
    omega
  let u := 256*(k/65536)+201
  have hu : u%256=201 := by dsimp [u]; omega
  have hk : k=256*u+51 := by
    have hdecomp := Nat.mod_add_div k 65536
    rw [hkmod] at hdecomp
    dsimp [u]
    omega
  rw [hk]
  intro hr
  exact (source_rectangle_u201_mod256 u hu)
    (BB6.Agent13One307.four_step_to_rectangle u hr)

theorem low_stop_m67_z21_mod128_unreachable
    (z m k : Nat) (hm : m=512*z+67) (hz : z%128=21)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 65536 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^16 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^16=65536 by decide] using h
  have hpmod : (2^(2*m+3))%65536=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hkmod : k%65536=33075 := by
    have hs : (k+3*m+4)%65536=0 := by
      rw [hstop]
      exact hpmod
    rw [hm] at hs
    omega
  let u := 256*(k/65536)+129
  have hu : u%256=129 := by dsimp [u]; omega
  have hk : k=256*u+51 := by
    have hdecomp := Nat.mod_add_div k 65536
    rw [hkmod] at hdecomp
    dsimp [u]
    omega
  rw [hk]
  intro hr
  exact (source_rectangle_u129_mod256 u hu)
    (BB6.Agent13One307.four_step_to_rectangle u hr)

#print axioms low_stop_m67_z9_mod128_unreachable
#print axioms low_stop_m67_z21_mod128_unreachable
end BB6.Agent13U201U129
