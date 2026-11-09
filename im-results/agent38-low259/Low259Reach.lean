import Low259Inverse
import OddOddLowVal
import EvenEvenInverse
import Agent3COrbitIff
import Agent3CImage
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace BB6.Agent38Low259
open BB6.Agent46

/-- Source-image obstruction, including the distinct time-zero blank seed. -/
theorem blank_no_odd_one (x y : Nat) (hy : 5≤y) (ho : y%2=1)
    (hs : (x+y)%4=1) : ¬ BB6.Agent3.CReach x y := by
  rintro ⟨time,hr⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hr
      omega
  | succ t =>
      have hh := BB6.Agent3.blank_section_odd_image t x y hr hy ho
      omega

/-- A forced affine predecessor of the central even/even branch violates
    the original source's odd-image theorem. -/
theorem blank_no_mid (q : Nat) :
    ¬ BB6.Agent3.CReach (160*q+78) (432*q+212) := by
  rintro ⟨time,hr⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hr
      omega
  | succ t =>
      cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at hr
      | some p =>
          rcases p with ⟨a,k⟩
          have hedge : secNext (a,k)=some (160*q+78,432*q+212) := by
            simpa [BB6.Agent8Section.run,hp] using hr
          obtain ⟨ha,hk⟩ := BB6.Agent46.section_even_sum_two_mod4_inverse
            a k (160*q+78) (432*q+212) (by omega) (by omega) (by omega) hedge
          have ha' : a=592*q+288 := by omega
          have hk' : k=216*q+105 := by omega
          have hpre : BB6.Agent3.CReach (592*q+288) (216*q+105) := by
            refine ⟨t,?_⟩
            simpa [ha',hk'] using hp
          exact blank_no_odd_one (592*q+288) (216*q+105)
            (by omega) (by omega) (by omega) hpre

/-- Every exact original-blank section state in this infinite even/even
    ray is excluded by a complete three-parent source inversion. -/
theorem blank_no_parent (q : Nat) :
    ¬ BB6.Agent3.CReach (256*q+128) (384*q+192) := by
  rintro ⟨time,hr⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hr
      omega
  | succ t =>
      cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at hr
      | some p =>
          rcases p with ⟨a,k⟩
          have hedge : secNext (a,k)=some (256*q+128,384*q+192) := by
            simpa [BB6.Agent8Section.run,hp] using hr
          have hparent := p_parent_source q a k hedge
          rcases hparent with hF | hQ | hD
          · obtain ⟨ha,hk⟩ := hF
            have hpre : BB6.Agent3.CReach (40*q+18) (492*q+239) := by
              refine ⟨t,?_⟩
              simpa [ha,hk] using hp
            exact blank_no_odd_one (40*q+18) (492*q+239)
              (by omega) (by omega) (by omega) hpre
          · obtain ⟨ha,hk⟩ := hQ
            have hpre : BB6.Agent3.CReach (160*q+78) (432*q+212) := by
              refine ⟨t,?_⟩
              simpa [ha,hk] using hp
            exact blank_no_mid q hpre
          · obtain ⟨ha,hk⟩ := hD
            have hpre : BB6.Agent3.CReach (640*q+318) (192*q+95) := by
              refine ⟨t,?_⟩
              simpa [ha,hk] using hp
            exact blank_no_odd_one (640*q+318) (192*q+95)
              (by omega) (by omega) (by omega) hpre

/-- Every genuine Machine C section output on the (1,259) modulo 512
    ray is unreachable, with no bound on q or the number of section calls. -/
theorem blank_no_first_259 (q : Nat) :
    ¬ BB6.Agent3.CReach 1 (512*q+259) := by
  intro h
  have hparent := (BB6.Agent3.oddodd_lowval_blank_reach_iff
    1 (512*q+259) (by decide) (by omega) (by omega) (by omega)
    (by omega) (by omega)).mp h
  have ha : (1+(512*q+259)-4)/2=256*q+128 := by omega
  have hk : (1+3*(512*q+259)-10)/4=384*q+192 := by omega
  have hpre : BB6.Agent3.CReach (256*q+128) (384*q+192) := by
    simpa only [BB6.Agent3.CReach,ha,hk] using hparent
  exact blank_no_parent q hpre

/-- An infinite class of exact Machine C first stopping-gate parameters. -/
theorem first_stop_m83_mod512 (m k : Nat)
    (hm : m%512=83)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hm83 : 83≤m := by omega
  have hpow : 512 ∣ (2:Nat)^(2*m+3) := by
    change (2:Nat)^9 ∣ (2:Nat)^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hsum : (k+3*m+4)%512=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hkmod : k%512=259 := by omega
  have hk : k=512*(k/512)+259 := by omega
  rw [hk]
  exact blank_no_first_259 (k/512)

#print axioms blank_no_mid
#print axioms blank_no_parent
#print axioms blank_no_first_259
#print axioms first_stop_m83_mod512
end BB6.Agent38Low259
