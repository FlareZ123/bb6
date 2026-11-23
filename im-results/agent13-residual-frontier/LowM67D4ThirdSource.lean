import LowM67D4SecondSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13D4Third
open BB6.Agent46 BB6.Agent3

/-- A third exact valuation-six rectangle, using a new depth-four B-O-B-F
    forced source path. This is disjoint from both earlier source exclusions
    for the same Machine C low-stop index progression. -/
theorem source_rectangle_u3449_mod8192
    (u : Nat) (hu : u%8192=3449) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  let t := u/8192
  have hU : u=8192*t+3449 := by
    have hh := Nat.mod_add_div u 8192
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
    have ha : a=(1417216*t+596701) := by
      simp at hpow
      omega
    have hk : k=(1388544*t+584629) := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))) hpre
  · subst n
    have ha : a=(354304*t+149173) := by
      simp at hpow
      omega
    have hk : k=(1920000*t+808390) := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    have hg1 := (BB6.Agent46.six_even_right_blank_reach_iff
      (354304*t+149173) (1920000*t+808390)
      (by omega) (by omega) (by omega) (by omega)).mp hpre
    have h1 : BB6.Agent3.CReach (2274304*t+957561) (960000*t+404194) := by
      simpa only [BB6.Agent3.CReach,
        show ((354304*t+149173))+((1920000*t+808390))-2=(2274304*t+957561) by omega,
        show (((1920000*t+808390))-2)/2=(960000*t+404194) by omega] using hg1
    have hg2 := (BB6.Agent46.six_even_right_blank_reach_iff
      (2274304*t+957561) (960000*t+404194)
      (by omega) (by omega) (by omega) (by omega)).mp h1
    have h2 : BB6.Agent3.CReach (3234304*t+1361753) (480000*t+202096) := by
      simpa only [BB6.Agent3.CReach,
        show ((2274304*t+957561))+((960000*t+404194))-2=(3234304*t+1361753) by omega,
        show (((960000*t+404194))-2)/2=(480000*t+202096) by omega] using hg2
    have hg3 := (BB6.Agent15.blank_reach_iff_affine
      (3234304*t+1361753) (480000*t+202096)
      (by omega) (by omega) (by omega)).mp h2
    have h3 : BB6.Agent3.CReach (3714304*t+1563847) (240000*t+101047) := by
      simpa only [BB6.Agent3.CReach,
        show ((3234304*t+1361753))+((480000*t+202096))-2=(3714304*t+1563847) by omega,
        show (((480000*t+202096))-2)/2=(240000*t+101047) by omega] using hg3
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))) h3
  · subst n
    have ha : a=(88576*t+37291) := by
      simp at hpow
      omega
    have hk : k=(2052864*t+864328) := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    have hg1 := (BB6.Agent46.six_even_right_blank_reach_iff
      (88576*t+37291) (2052864*t+864328)
      (by omega) (by omega) (by omega) (by omega)).mp hpre
    have h1 : BB6.Agent3.CReach (2141440*t+901617) (1026432*t+432163) := by
      simpa only [BB6.Agent3.CReach,
        show ((88576*t+37291))+((2052864*t+864328))-2=(2141440*t+901617) by omega,
        show (((2052864*t+864328))-2)/2=(1026432*t+432163) by omega] using hg1
    have hg2 := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (2141440*t+901617) (1026432*t+432163)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp h1
    have h2 : BB6.Agent3.CReach (1583936*t+666888) (1305184*t+549524) := by
      simpa only [BB6.Agent3.CReach,
        show (((2141440*t+901617))+((1026432*t+432163))-4)/2=(1583936*t+666888) by omega,
        show (((2141440*t+901617))+3*((1026432*t+432163))-10)/4=(1305184*t+549524) by omega] using hg2
    have hg3 := (BB6.Agent46.six_even_right_blank_reach_iff
      (1583936*t+666888) (1305184*t+549524)
      (by omega) (by omega) (by omega) (by omega)).mp h2
    have h3 : BB6.Agent3.CReach (2889120*t+1216410) (652592*t+274761) := by
      simpa only [BB6.Agent3.CReach,
        show ((1583936*t+666888))+((1305184*t+549524))-2=(2889120*t+1216410) by omega,
        show (((1305184*t+549524))-2)/2=(652592*t+274761) by omega] using hg3
    have hg4 := (BB6.Agent3.evenodd_four_blank_reach_iff
      (2889120*t+1216410) (652592*t+274761)
      (by omega) (by omega) (by omega) (by omega)).mp h3
    have h4 : BB6.Agent3.CReach (1770856*t+745583) (1211724*t+510171) := by
      simpa only [BB6.Agent3.CReach,
        show (((2889120*t+1216410))+((652592*t+274761))-5)/2=(1770856*t+745583) by omega,
        show (((2889120*t+1216410))+3*((652592*t+274761))-9)/4=(1211724*t+510171) by omega] using hg4
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))) h4

/-- Every low stopping target with m=512*z+67 and z congruent 3521
    modulo 4096 is absent from the authentic Machine C blank section. -/
theorem low_stop_m67_z3521_mod4096_unreachable
    (z m k : Nat) (hm : m=512*z+67) (hz : z%4096=3521)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 2097152 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^21 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^21=2097152 by decide] using h
  have hpmod : (2^(2*m+3))%2097152=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hkmod : k%2097152=882995 := by
    have hs : (k+3*m+4)%2097152=0 := by
      rw [hstop]
      exact hpmod
    rw [hm] at hs
    omega
  let u := 8192*(k/2097152)+3449
  have hu : u%8192=3449 := by dsimp [u]; omega
  have hk : k=256*u+51 := by
    have hh := Nat.mod_add_div k 2097152
    rw [hkmod] at hh
    dsimp [u]
    omega
  rw [hk]
  intro hr
  exact (source_rectangle_u3449_mod8192 u hu)
    (BB6.Agent13One307.four_step_to_rectangle u hr)

#print axioms source_rectangle_u3449_mod8192
#print axioms low_stop_m67_z3521_mod4096_unreachable
end BB6.Agent13D4Third
