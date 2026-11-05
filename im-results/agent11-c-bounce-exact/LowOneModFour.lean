import Agent3COrbitIff
import SectionParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Low
open BB6.Agent46

/-- No original Machine C section input produces (1,y) when y>=5 and y=1 mod 4. -/
theorem source_no_one_one (a k y : Nat) (hy : 5 ≤ y) (hmod : y % 4 = 1) :
    secNext (a,k) ≠ some (1,y) := by
  intro h
  have hodd : y % 2 = 1 := by omega
  have hi := BB6.Agent3.section_odd_image a k 1 y h hy hodd
  omega

/-- This missing image cylinder is also disjoint from the real blank orbit. -/
theorem blank_no_one_one (y : Nat) (hy : 5 ≤ y) (hmod : y % 4 = 1) :
    ¬ BB6.Agent3.CReach 1 y := by
  rintro ⟨time, h⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at h
  | succ t =>
      have hodd : y % 2 = 1 := by omega
      have hi := BB6.Agent3.blank_section_odd_image t 1 y h hy hodd
      omega

private theorem low_succ_power (n : Nat) :
    3*(n+1)+9 ≤ 2^(2*(n+1)+3) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : 2*(n+1+1)+3 = (2*(n+1)+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- All low stopping inputs indexed by m=1 (mod 4) are source-authentic
    halting sections but genuinely unreachable from the blank entry (5,1). -/
theorem blank_no_low_m_one_mod_four (m k : Nat)
    (hm : m % 4 = 1)
    (hgate : k+3*m+4 = 2^(2*m+3)) :
    secNext (1,k)=none ∧ ¬ BB6.Agent3.CReach 1 k := by
  have hm1 : 1 ≤ m := by omega
  have hdiv : 4 ∣ 2^(2*m+3) := by
    change 2^2 ∣ 2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hsum : (k+3*m+4)%4=0 := by
    rw [hgate]
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hkmod : k%4=1 := by omega
  have hmrepr : m = (m-1)+1 := by omega
  have hpow := low_succ_power (m-1)
  have hgate' := hgate
  rw [hmrepr] at hgate'
  have hk5 : 5 ≤ k := by omega
  constructor
  · apply (BB6.Agent15.section_halts_iff_parametric _ _).mpr
    right
    left
    exact ⟨rfl,m,hgate⟩
  · exact blank_no_one_one k hk5 hkmod

#print axioms source_no_one_one
#print axioms blank_no_one_one
#print axioms blank_no_low_m_one_mod_four
end BB6.Agent11Low
