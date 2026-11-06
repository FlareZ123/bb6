import OddOddLowVal
import Agent3COrbitIff
import SectionParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Low
open BB6.Agent46

private theorem low_margin (n : Nat) :
    3*(n+1)+27 ≤ 2^(2*(n+1)+3) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : 2*(n+1+1)+3=(2*(n+1)+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- The low stopping indices m=7 modulo 16 have one forced original
    odd/odd predecessor, which is absent from the authentic blank orbit. -/
theorem blank_no_low_m_seven_mod16 (m k : Nat)
    (hm : m%16=7)
    (hgate : k+3*m+4=2^(2*m+3)) :
    secNext (1,k)=none ∧ ¬ BB6.Agent3.CReach 1 k := by
  have hm1 : 1≤m := by omega
  have hbig : 3*m+27 ≤ 2^(2*m+3) := by
    obtain ⟨t,ht⟩ : ∃ t, m=t+1 := ⟨m-1,by omega⟩
    subst m
    exact low_margin t
  have hk23 : 23≤k := by omega
  have hdiv : 16 ∣ 2^(2*m+3) := by
    change 2^4 ∣ 2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hmod : (k+3*m+4)%16=0 := by
    rw [hgate]
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hkmod : k%16=7 := by omega
  have hodd : k%2=1 := by omega
  have hsum4 : (1+k)%4=0 := by omega
  have hsum16 : (1+k)%16≠0 := by omega
  have hsumBig : 24≤1+k := by omega
  have hparent := BB6.Agent3.oddodd_lowval_blank_reach_iff
     1 k (by decide) hodd (by omega) hsum4 hsum16 hsumBig
  have hBodd : ((1+3*k-10)/4)%2=1 := by omega
  have hBbig : 5≤((1+3*k-10)/4) := by omega
  have hPbad : (((1+k-4)/2)+((1+3*k-10)/4))%4=1 := by omega
  constructor
  · apply (BB6.Agent15.section_halts_iff_parametric _ _).mpr
    right
    left
    exact ⟨rfl,m,hgate⟩
  · intro hr
    obtain ⟨time,hp⟩ := hparent.mp hr
    cases time with
    | zero =>
        simp [BB6.Agent8Section.run] at hp
        omega
    | succ t =>
        have hi := BB6.Agent3.blank_section_odd_image t
          ((1+k-4)/2) ((1+3*k-10)/4) hp hBbig hBodd
        omega

#print axioms blank_no_low_m_seven_mod16
end BB6.Agent11Low
