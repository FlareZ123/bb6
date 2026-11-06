import OddOddLowVal
import EvenRightSixOrbit
import Agent3COrbitIff
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace BB6.Agent19Low427
open BB6.Agent46 BB6.Agent3

/-- Seven source-exact forced backward sections exclude an infinite
Machine C target cylinder. The small q=0 exception is left undecided. -/
theorem blank_no_one_427_mod1024 (q : Nat) (hq : 1≤q) :
    ¬ BB6.Agent3.CReach 1 (1024*q+427) := by
  intro hr0
  have hr1 : BB6.Agent3.CReach (512*q+212) (768*q+318) := by
    have h := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (1) (1024*q+427)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp hr0
    change BB6.Agent3.CReach _ _ at h
    have ha : ((1)+(1024*q+427)-4)/2=512*q+212 := by omega
    have hk : ((1)+3*(1024*q+427)-10)/4=768*q+318 := by omega
    simpa only [ha,hk] using h
  have hr2 : BB6.Agent3.CReach (1280*q+528) (384*q+158) := by
    have h := (BB6.Agent46.six_even_right_blank_reach_iff
      (512*q+212) (768*q+318)
      (by omega) (by omega) (by omega) (by omega)).mp hr1
    have ha : (512*q+212)+(768*q+318)-2=1280*q+528 := by omega
    have hk : ((768*q+318)-2)/2=384*q+158 := by omega
    simpa only [ha,hk] using h
  have hr3 : BB6.Agent3.CReach (1664*q+684) (192*q+78) := by
    have h := (BB6.Agent46.six_even_right_blank_reach_iff
      (1280*q+528) (384*q+158)
      (by omega) (by omega) (by omega) (by omega)).mp hr2
    have ha : (1280*q+528)+(384*q+158)-2=1664*q+684 := by omega
    have hk : ((384*q+158)-2)/2=192*q+78 := by omega
    simpa only [ha,hk] using h
  have hr4 : BB6.Agent3.CReach (1856*q+760) (96*q+38) := by
    have h := (BB6.Agent46.six_even_right_blank_reach_iff
      (1664*q+684) (192*q+78)
      (by omega) (by omega) (by omega) (by omega)).mp hr3
    have ha : (1664*q+684)+(192*q+78)-2=1856*q+760 := by omega
    have hk : ((192*q+78)-2)/2=96*q+38 := by omega
    simpa only [ha,hk] using h
  have hr5 : BB6.Agent3.CReach (1952*q+796) (48*q+18) := by
    have h := (BB6.Agent46.six_even_right_blank_reach_iff
      (1856*q+760) (96*q+38)
      (by omega) (by omega) (by omega) (by omega)).mp hr4
    have ha : (1856*q+760)+(96*q+38)-2=1952*q+796 := by omega
    have hk : ((96*q+38)-2)/2=48*q+18 := by omega
    simpa only [ha,hk] using h
  have hr6 : BB6.Agent3.CReach (2000*q+812) (24*q+8) := by
    have h := (BB6.Agent46.six_even_right_blank_reach_iff
      (1952*q+796) (48*q+18)
      (by omega) (by omega) (by omega) (by omega)).mp hr5
    have ha : (1952*q+796)+(48*q+18)-2=2000*q+812 := by omega
    have hk : ((48*q+18)-2)/2=24*q+8 := by omega
    simpa only [ha,hk] using h
  have hr7 : BB6.Agent3.CReach (2024*q+818) (12*q+3) := by
    have h := (BB6.Agent46.six_even_right_blank_reach_iff
      (2000*q+812) (24*q+8)
      (by omega) (by omega) (by omega) (by omega)).mp hr6
    have ha : (2000*q+812)+(24*q+8)-2=2024*q+818 := by omega
    have hk : ((24*q+8)-2)/2=12*q+3 := by omega
    simpa only [ha,hk] using h
  rcases hr7 with ⟨time, htrace⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at htrace <;> omega
  | succ t =>
      have hi := BB6.Agent3.blank_section_odd_image t
        (2024*q+818) (12*q+3) htrace (by omega) (by omega)
      omega

/-- Uniform exponential lower bound ensuring a low stopping witness at m≥4
cannot have the exceptional initial cylinder quotient q=0. -/
private theorem first_power_large (m : Nat) (hm : 4≤m) :
    3*m+1455 ≤ (2:Nat)^(2*m+3) := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm4 : 4≤m
      · have hi := ih hm4
        have he : 2*(m+1)+3=(2*m+3)+2 := by omega
        rw [he,Nat.pow_add]
        have hfour : (2:Nat)^2=4 := by decide
        rw [hfour]
        omega
      · have meq : m=3 := by omega
        subst m
        decide

/-- An entire second first-family parameter class missed by the M512
quotient is excluded from the authentic source blank section orbit. -/
theorem low_m539_mod1024_unreachable (m k : Nat)
    (hm : m%1024=539)
    (hgate : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hm4 : 4≤m := by omega
  have hpow : 1024 ∣ (2:Nat)^(2*m+3) := by
    have h : (2:Nat)^10 ∣ (2:Nat)^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa using h
  have hz : (k+3*m+4)%1024=0 := by
    rw [hgate]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hk : k%1024=427 := by omega
  have hlarge : 1451≤k := by
    have hi := first_power_large m hm4
    omega
  have hrepr : k=1024*(k/1024)+427 := by omega
  have hq : 1≤k/1024 := by omega
  rw [hrepr]
  exact blank_no_one_427_mod1024 (k/1024) hq

#print axioms blank_no_one_427_mod1024
#print axioms low_m539_mod1024_unreachable
end BB6.Agent19Low427
