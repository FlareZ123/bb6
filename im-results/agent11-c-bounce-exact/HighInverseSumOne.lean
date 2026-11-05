import OddOddLowVal
import HighSumTwo
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11High

private theorem high_gap (n : Nat) :
    3*(n+2)+40 ≤ 3*2^(2*(n+2)+2) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : 2*(n+1+2)+2=(2*(n+2)+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- Uniform two-step true-blank obstruction: the high stopping gate has a
    unique odd/odd predecessor whose own odd-right sum is 1 modulo 4. -/
theorem blank_no_high_jplusm_six_mod16 (j m k : Nat)
    (hm : 2≤m)
    (hjm : (j+m)%16=6)
    (hm4 : m%4≠1)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  have hgap : 3*m+40 ≤ 3*2^(2*m+2) := by
    obtain ⟨t,ht⟩ : ∃ t, m=t+2 := ⟨m-2,by omega⟩
    subst m
    exact high_gap t
  have hpow : 1≤2^(2*m+2) := Nat.pow_pos (by decide)
  have hJ : j≤2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow
  have hmul : 2^(2*m+2)*(j+3)=2^(2*m+2)*j+3*2^(2*m+2) := by
    simp [Nat.mul_add,Nat.mul_comm]
  have hk35 : 35≤k := by
    rw [hmul] at hgate
    omega
  have hdiv : 16 ∣ 2^(2*m+2) := by
    change 2^4 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hprod : 16 ∣ 2^(2*m+2)*(j+3) := by
    rcases hdiv with ⟨q,hq⟩
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hzero : (k+j+3*m+5)%16=0 := by
    rw [hgate]
    exact Nat.mod_eq_zero_of_dvd hprod
  have hxo : (2*j+3)%2=1 := by omega
  have hyo : k%2=1 := by omega
  have hsum4 : ((2*j+3)+k)%4=0 := by omega
  have hsum16 : ((2*j+3)+k)%16≠0 := by omega
  have hsumBig : 24≤(2*j+3)+k := by omega
  have hparent := BB6.Agent3.oddodd_lowval_blank_reach_iff
     (2*j+3) k hxo hyo (by omega) hsum4 hsum16 hsumBig
  have hBodd : (((2*j+3)+3*k-10)/4)%2=1 := by omega
  have hBbig : 5≤((2*j+3)+3*k-10)/4 := by omega
  have hPbad : (((2*j+3+k-4)/2)+(((2*j+3)+3*k-10)/4))%4=1 := by omega
  intro hr
  obtain ⟨time,hp⟩ := hparent.mp hr
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hp
      omega
  | succ t =>
      have hi := BB6.Agent3.blank_section_odd_image t
        ((2*j+3+k-4)/2) (((2*j+3)+3*k-10)/4)
        hp hBbig hBodd
      omega

#print axioms blank_no_high_jplusm_six_mod16
end BB6.Agent11High
