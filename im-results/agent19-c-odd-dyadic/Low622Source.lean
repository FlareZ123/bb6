import OddSevenForcedRoot
import EvenRightSixOrbit
import ReachAffine
import OddOddLowVal
import Agent3COrbitIff
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Low622
open BB6.Agent46 BB6.Agent3

/-- Seven authentic source-inverse returns exclude every terminal right
counter congruent to 622 modulo 1024, beyond the finite M512 quotient. -/
theorem blank_no_one_622_mod1024 (q : Nat) :
    ¬ BB6.Agent3.CReach 1 (1024*q+622) := by
  intro hr0
  have hr1 : BB6.Agent3.CReach (1024*q+621) (512*q+310) := by
    have h := (BB6.Agent19Seven.sumseven_forced_root_iff 1 (1024*q+622)
      (by omega) (by omega) (by omega) (by omega)).mp hr0
    have ha : 1+(1024*q+622)-2=1024*q+621 := by omega
    have hk : ((1024*q+622)-2)/2=512*q+310 := by omega
    simpa only [ha, hk] using h
  have hr2 : BB6.Agent3.CReach (1536*q+929) (256*q+154) := by
    have h := (BB6.Agent46.six_even_right_blank_reach_iff
      (1024*q+621) (512*q+310)
      (by omega) (by omega) (by omega) (by omega)).mp hr1
    have ha : (1024*q+621)+(512*q+310)-2=1536*q+929 := by omega
    have hk : ((512*q+310)-2)/2=256*q+154 := by omega
    simpa only [ha, hk] using h
  have hr3 : BB6.Agent3.CReach (1792*q+1081) (128*q+76) := by
    have h := (BB6.Agent46.six_even_right_blank_reach_iff
      (1536*q+929) (256*q+154)
      (by omega) (by omega) (by omega) (by omega)).mp hr2
    have ha : (1536*q+929)+(256*q+154)-2=1792*q+1081 := by omega
    have hk : ((256*q+154)-2)/2=128*q+76 := by omega
    simpa only [ha, hk] using h
  have hr4 : BB6.Agent3.CReach (1920*q+1155) (64*q+37) := by
    have h := (BB6.Agent15.blank_reach_iff_affine
      (1792*q+1081) (128*q+76)
      (by omega) (by omega) (by omega)).mp hr3
    change BB6.Agent3.CReach _ _ at h
    have ha : (1792*q+1081)+(128*q+76)-2=1920*q+1155 := by omega
    have hk : ((128*q+76)-2)/2=64*q+37 := by omega
    simpa only [ha, hk] using h
  have hr5 : BB6.Agent3.CReach (992*q+594) (528*q+314) := by
    have h := (BB6.Agent3.oddodd_lowval_blank_reach_iff
      (1920*q+1155) (64*q+37)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp hr4
    have ha : ((1920*q+1155)+(64*q+37)-4)/2=992*q+594 := by omega
    have hk : ((1920*q+1155)+3*(64*q+37)-10)/4=528*q+314 := by omega
    simpa only [ha, hk] using h
  have hr6 : BB6.Agent3.CReach (1520*q+906) (264*q+156) := by
    have h := (BB6.Agent46.six_even_right_blank_reach_iff
      (992*q+594) (528*q+314)
      (by omega) (by omega) (by omega) (by omega)).mp hr5
    have ha : (992*q+594)+(528*q+314)-2=1520*q+906 := by omega
    have hk : ((528*q+314)-2)/2=264*q+156 := by omega
    simpa only [ha, hk] using h
  have hr7 : BB6.Agent3.CReach (1784*q+1060) (132*q+77) := by
    have h := (BB6.Agent46.six_even_right_blank_reach_iff
      (1520*q+906) (264*q+156)
      (by omega) (by omega) (by omega) (by omega)).mp hr6
    have ha : (1520*q+906)+(264*q+156)-2=1784*q+1060 := by omega
    have hk : ((264*q+156)-2)/2=132*q+77 := by omega
    simpa only [ha, hk] using h
  rcases hr7 with ⟨time, htrace⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at htrace <;> omega
  | succ t =>
      have hi := BB6.Agent3.blank_section_odd_image t
        (1784*q+1060) (132*q+77) htrace (by omega) (by omega)
      omega

/-- Entire low stopping family m congruent to 474 modulo 1024 misses
    the genuine Machine C blank section orbit for every parameter. -/
theorem low_m474_mod1024_unreachable (m k : Nat)
    (hm : m%1024=474)
    (hgate : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hm5 : 5≤m := by omega
  have hpow : 1024 ∣ (2:Nat)^(2*m+3) := by
    have h : (2:Nat)^10 ∣ (2:Nat)^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa using h
  have hz : (k+3*m+4)%1024=0 := by
    rw [hgate]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hk : k%1024=622 := by omega
  have hrepr : k=1024*(k/1024)+622 := by omega
  rw [hrepr]
  exact blank_no_one_622_mod1024 (k/1024)

#print axioms blank_no_one_622_mod1024
#print axioms low_m474_mod1024_unreachable
end BB6.Agent19Low622
