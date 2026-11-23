import LowM67D4Source
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13D4Second
open BB6.Agent46 BB6.Agent3

/-- A second valuation-six source rectangle, disjoint from the previously
    excluded u=633 mod1024 ray. Every original predecessor has depth
    zero, two, or four, and each reaches a forbidden blank-image cell
    after at most four exact backward steps. -/
theorem source_rectangle_u1913_mod4096
    (u : Nat) (hu : u%4096=1913) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  let t := u/4096
  have hU : u=4096*t+1913 := by
    have hh := Nat.mod_add_div u 4096
    dsimp [t]
    omega
  have hx : 5<180*u+28 := by omega
  have hxe : (180*u+28)%2=0 := by omega
  have hyo : (166*u+25)%2=1 := by omega
  have hy5 : 5≤166*u+25 := by omega
  have hbig : 128≤(180*u+28)+(166*u+25)+1 := by omega
  have hmod : ((180*u+28)+(166*u+25)+1)%128=64 := by
    rw [hU]
    omega
  intro hr
  obtain ⟨a,k,hpre,hedge⟩ :=
    BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
      (180*u+28) (166*u+25) hx hr
  obtain ⟨n,hn,hlow,hpow,hcost⟩ :=
    BB6.Agent13ValSixFan.even_odd_valuation_six_parent
      a k (180*u+28) (166*u+25)
      hxe hyo hy5 hbig hmod hedge
  rw [hU] at hpow hcost
  rcases hn with hn0|hn2|hn4
  · subst n
    have ha : a=(708608*t+330973) := by
      simp at hpow
      omega
    have hk : k=(694272*t+324277) := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))) hpre
  · subst n
    have ha : a=(177152*t+82741) := by
      simp at hpow
      omega
    have hk : k=(960000*t+448390) := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    have hg1 := (BB6.Agent46.six_even_right_blank_reach_iff
      (177152*t+82741) (960000*t+448390)
      (by omega) (by omega) (by omega) (by omega)).mp hpre
    have h1 : BB6.Agent3.CReach (1137152*t+531129) (480000*t+224194) := by
      simpa only [BB6.Agent3.CReach,
        show ((177152*t+82741))+((960000*t+448390))-2=(1137152*t+531129) by omega,
        show (((960000*t+448390))-2)/2=(480000*t+224194) by omega] using hg1
    have hg2 := (BB6.Agent46.six_even_right_blank_reach_iff
      (1137152*t+531129) (480000*t+224194)
      (by omega) (by omega) (by omega) (by omega)).mp h1
    have h2 : BB6.Agent3.CReach (1617152*t+755321) (240000*t+112096) := by
      simpa only [BB6.Agent3.CReach,
        show ((1137152*t+531129))+((480000*t+224194))-2=(1617152*t+755321) by omega,
        show (((480000*t+224194))-2)/2=(240000*t+112096) by omega] using hg2
    have hg3 := (BB6.Agent15.blank_reach_iff_affine
      (1617152*t+755321) (240000*t+112096)
      (by omega) (by omega) (by omega)).mp h2
    have h3 : BB6.Agent3.CReach (1857152*t+867415) (120000*t+56047) := by
      simpa only [BB6.Agent3.CReach,
        show ((1617152*t+755321))+((240000*t+112096))-2=(1857152*t+867415) by omega,
        show (((240000*t+112096))-2)/2=(120000*t+56047) by omega] using hg3
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))) h3
  · subst n
    have ha : a=(44288*t+20683) := by
      simp at hpow
      omega
    have hk : k=(1026432*t+479416) := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    have hg1 := (BB6.Agent46.six_even_right_blank_reach_iff
      (44288*t+20683) (1026432*t+479416)
      (by omega) (by omega) (by omega) (by omega)).mp hpre
    have h1 : BB6.Agent3.CReach (1070720*t+500097) (513216*t+239707) := by
      simpa only [BB6.Agent3.CReach,
        show ((44288*t+20683))+((1026432*t+479416))-2=(1070720*t+500097) by omega,
        show (((1026432*t+479416))-2)/2=(513216*t+239707) by omega] using hg1
    have hg2 := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (1070720*t+500097) (513216*t+239707)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp h1
    have h2 : BB6.Agent3.CReach (791968*t+369900) (652592*t+304802) := by
      simpa only [BB6.Agent3.CReach,
        show (((1070720*t+500097))+((513216*t+239707))-4)/2=(791968*t+369900) by omega,
        show (((1070720*t+500097))+3*((513216*t+239707))-10)/4=(652592*t+304802) by omega] using hg2
    have hg3 := (BB6.Agent46.six_even_right_blank_reach_iff
      (791968*t+369900) (652592*t+304802)
      (by omega) (by omega) (by omega) (by omega)).mp h2
    have h3 : BB6.Agent3.CReach (1444560*t+674700) (326296*t+152400) := by
      simpa only [BB6.Agent3.CReach,
        show ((791968*t+369900))+((652592*t+304802))-2=(1444560*t+674700) by omega,
        show (((652592*t+304802))-2)/2=(326296*t+152400) by omega] using hg3
    have hg4 := (BB6.Agent46.six_even_right_blank_reach_iff
      (1444560*t+674700) (326296*t+152400)
      (by omega) (by omega) (by omega) (by omega)).mp h3
    have h4 : BB6.Agent3.CReach (1770856*t+827098) (163148*t+76199) := by
      simpa only [BB6.Agent3.CReach,
        show ((1444560*t+674700))+((326296*t+152400))-2=(1770856*t+827098) by omega,
        show (((326296*t+152400))-2)/2=(163148*t+76199) by omega] using hg4
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inl (by omega))) h4

/-- A new infinite source-authentic necessary low-stop exclusion:
    m=512*z+67 and z=1729 (mod 2048). This is an all-time claim
    about the original Machine C blank section, not a halt decision. -/
theorem low_stop_m67_z1729_mod2048_unreachable
    (z m k : Nat) (hm : m=512*z+67) (hz : z%2048=1729)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 1048576 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^20 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^20=1048576 by decide] using h
  have hpmod : (2^(2*m+3))%1048576=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hkmod : k%1048576=489779 := by
    have hs : (k+3*m+4)%1048576=0 := by
      rw [hstop]
      exact hpmod
    rw [hm] at hs
    omega
  let u := 4096*(k/1048576)+1913
  have hu : u%4096=1913 := by dsimp [u]; omega
  have hk : k=256*u+51 := by
    have hh := Nat.mod_add_div k 1048576
    rw [hkmod] at hh
    dsimp [u]
    omega
  rw [hk]
  intro hr
  exact (source_rectangle_u1913_mod4096 u hu)
    (BB6.Agent13One307.four_step_to_rectangle u hr)

#print axioms source_rectangle_u1913_mod4096
#print axioms low_stop_m67_z1729_mod2048_unreachable
end BB6.Agent13D4Second
