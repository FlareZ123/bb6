import EvenOddValuationSix
import One307Source
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13D4Low
open BB6.Agent46 BB6.Agent3

/-- In the nontrivial valuation-six source sector the full original
    inverse has only bounce parents n=0,2,4. For this specific infinite
    affine cylinder each of those parents has a bounded source-verified
    forced path to an impossible odd-right blank-image congruence.
    This proof does not use any finite quotient or orbit-time cutoff. -/
theorem source_rectangle_u633_mod1024
    (u : Nat) (hu : u%1024=633) :
    ¬ BB6.Agent3.CReach (180*u+28) (166*u+25) := by
  let t := u/1024
  have hU : u=1024*t+633 := by
    have hh := Nat.mod_add_div u 1024
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
    have ha : a=177152*t+109533 := by
      simp at hpow
      omega
    have hk : k=173568*t+107317 := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))) hpre
  · subst n
    have ha : a=44288*t+27381 := by
      simp at hpow
      omega
    have hk : k=240000*t+148390 := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    have hB1 := (BB6.Agent46.six_even_right_blank_reach_iff
      (44288*t+27381) (240000*t+148390)
      (by omega) (by omega) (by omega) (by omega)).mp hpre
    have h1 : BB6.Agent3.CReach (284288*t+175769) (120000*t+74194) := by
      simpa only [BB6.Agent3.CReach,
        show (44288*t+27381)+(240000*t+148390)-2=
          284288*t+175769 by omega,
        show ((240000*t+148390)-2)/2=
          120000*t+74194 by omega] using hB1
    have hB2 := (BB6.Agent46.six_even_right_blank_reach_iff
      (284288*t+175769) (120000*t+74194)
      (by omega) (by omega) (by omega) (by omega)).mp h1
    have h2 : BB6.Agent3.CReach (404288*t+249961) (60000*t+37096) := by
      simpa only [BB6.Agent3.CReach,
        show (284288*t+175769)+(120000*t+74194)-2=
          404288*t+249961 by omega,
        show ((120000*t+74194)-2)/2=
          60000*t+37096 by omega] using hB2
    have hA := (BB6.Agent15.blank_reach_iff_affine
      (404288*t+249961) (60000*t+37096)
      (by omega) (by omega) (by omega)).mp h2
    have h3 : BB6.Agent3.CReach (464288*t+287055) (30000*t+18547) := by
      simpa only [BB6.Agent3.CReach,
        show (404288*t+249961)+(60000*t+37096)-2=
          464288*t+287055 by omega,
        show ((60000*t+37096)-2)/2=
          30000*t+18547 by omega] using hA
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inr (by omega))) h3
  · subst n
    have ha : a=11072*t+6843 := by
      simp at hpow
      omega
    have hk : k=256608*t+158656 := by
      simp at hcost
      omega
    rw [ha,hk] at hpre
    have hB := (BB6.Agent46.six_even_right_blank_reach_iff
      (11072*t+6843) (256608*t+158656)
      (by omega) (by omega) (by omega) (by omega)).mp hpre
    have h1 : BB6.Agent3.CReach (267680*t+165497) (128304*t+79327) := by
      simpa only [BB6.Agent3.CReach,
        show (11072*t+6843)+(256608*t+158656)-2=
          267680*t+165497 by omega,
        show ((256608*t+158656)-2)/2=
          128304*t+79327 by omega] using hB
    have hO := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (267680*t+165497) (128304*t+79327)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).mp h1
    have h2 : BB6.Agent3.CReach (197992*t+122410) (163148*t+100867) := by
      simpa only [BB6.Agent3.CReach,
        show ((267680*t+165497)+(128304*t+79327)-4)/2=
          197992*t+122410 by omega,
        show ((267680*t+165497)+3*(128304*t+79327)-10)/4=
          163148*t+100867 by omega] using hO
    exact (BB6.Agent13TwoParent.odd_forbidden_image _ _
      (by omega) (by omega) (Or.inl (by omega))) h2

/-- An additional, disjoint infinite low-stop necessary-family exclusion
    m=512*z+67, z=65 modulo 512. The family is outside the sixteen
    depth-0/2 classes and uses genuinely three original-source parents. -/
theorem low_stop_m67_z65_mod512_unreachable
    (z m k : Nat) (hm : m=512*z+67) (hz : z%512=65)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 262144 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^18 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^18=262144 by decide] using h
  have hpmod : (2^(2*m+3))%262144=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hkmod : k%262144=162099 := by
    have hs : (k+3*m+4)%262144=0 := by
      rw [hstop]
      exact hpmod
    rw [hm] at hs
    omega
  let u := 1024*(k/262144)+633
  have hu : u%1024=633 := by dsimp [u]; omega
  have hk : k=256*u+51 := by
    have hh := Nat.mod_add_div k 262144
    rw [hkmod] at hh
    dsimp [u]
    omega
  rw [hk]
  intro hr
  exact (source_rectangle_u633_mod1024 u hu)
    (BB6.Agent13One307.four_step_to_rectangle u hr)

#print axioms source_rectangle_u633_mod1024
#print axioms low_stop_m67_z65_mod512_unreachable
end BB6.Agent13D4Low
