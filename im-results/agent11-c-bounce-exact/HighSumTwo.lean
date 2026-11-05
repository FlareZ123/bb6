import Agent3COrbitIff
import SectionParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11High
open BB6.Agent46

private theorem high_power_margin (m : Nat) :
    3*m+12 ≤ 3*2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+2 = (2*m+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- Source exact missing-image cylinder, uniform in both counters. -/
theorem source_no_odd_sum_two (a k x y : Nat)
    (hy : 5≤y) (ho : y%2=1) (hs : (x+y)%4=2) :
    secNext (a,k) ≠ some (x,y) := by
  intro h
  have hi := BB6.Agent3.section_odd_image a k x y h hy ho
  omega

/-- The actual blank-section orbit never enters this cylinder. -/
theorem blank_no_odd_sum_two (x y : Nat)
    (hy : 5≤y) (ho : y%2=1) (hs : (x+y)%4=2) :
    ¬ BB6.Agent3.CReach x y := by
  rintro ⟨time,h⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at h
      omega
  | succ t =>
      have hi := BB6.Agent3.blank_section_odd_image t x y h hy ho
      omega

/-- Every high section stopping parameter j+m=0 mod4 has no genuine
    section predecessor and cannot appear in the original blank orbit. -/
theorem blank_no_high_jplusm_zero_modfour (j m k : Nat)
    (hpair : (j+m)%4=0)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    secNext (2*j+3,k)=none ∧ ¬ BB6.Agent3.CReach (2*j+3) k := by
  have hpow : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
  have hm := high_power_margin m
  have hk7 : 7 ≤ k := by
    have hmul : 2^(2*m+2)*(j+3)=
        2^(2*m+2)*j+3*2^(2*m+2) := by
      simp [Nat.mul_add, Nat.mul_comm]
    rw [hmul] at hgate
    omega
  have hdiv : 4 ∣ 2^(2*m+2) := by
    change 2^2 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hprod : 4 ∣ 2^(2*m+2)*(j+3) := by
    rcases hdiv with ⟨q,hq⟩
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hzero : (k+j+3*m+5)%4=0 := by
    rw [hgate]
    exact Nat.mod_eq_zero_of_dvd hprod
  have hodd : k%2=1 := by omega
  have hbad : ((2*j+3)+k)%4=2 := by omega
  constructor
  · apply (BB6.Agent15.section_halts_iff_parametric _ _).mpr
    right
    right
    exact ⟨j,m,rfl,hgate⟩
  · exact blank_no_odd_sum_two (2*j+3) k (by omega) hodd hbad

#print axioms source_no_odd_sum_two
#print axioms blank_no_odd_sum_two
#print axioms blank_no_high_jplusm_zero_modfour
end BB6.Agent11High
