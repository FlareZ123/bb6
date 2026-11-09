import UpperHighRootGap

namespace CascadeFastReturn
open CascadeBitSweep CascadeResetInverse CascadeUniformFatal CascadeSweep

private theorem middle_quotient_gap_two_three (k j q : Nat)
    (hl : 2*2^k<q) (hh : q<3*2^k)
    (hb : 6*2^j+1≤q ∧ q≤8*2^j-1) : False := by
  by_cases he : j+2≤k
  · have hpow : 2^(j+2)≤2^k :=
      Nat.pow_le_pow_right (by decide) he
    have heq : 2^(j+2)=4*2^j := by
      rw [show j+2=(j+1)+1 by omega, Nat.pow_succ, Nat.pow_succ]
      omega
    rw [heq] at hpow
    omega
  · have hkj : k≤j+1 := by omega
    have hpow : 2^k≤2^(j+1) :=
      Nat.pow_le_pow_right (by decide) hkj
    rw [Nat.pow_succ] at hpow
    omega

/-- A source odd first reset cannot land in the low middle band unless
    its exact offset 2h+5 is divisible by nine. The valuation-zero
    quotient would belong to the empty interval (2·2^k,3·2^k). -/
theorem middle_low_odd_output_mod_nine (a h k : Nat)
    (hodd : (a+firstFailIndex a)%2=1)
    (hout : bitOutcome a=some h)
    (hlow : 4*2^k≤h)
    (htop : 2*h+5<9*2^k) :
    (2*h+5)%9=0 := by
  let j := firstFailIndex a
  let q := 4*2^j+(a+j)/2+3
  let t := (stripTwos q).1
  let d := (stripTwos q).2
  have hnot : a+j+4≠4*2^j := by
    intro hf
    have hn : bitOutcome a=none := by simp [bitOutcome, j, hf]
    rw [hn] at hout
    cases hout
  have hpar : (a+j)%2=1 := hodd
  have hentry : h=(3^(t+1)*d-5)/2 := by
    have hne : (a+j)%2≠0 := by omega
    simp [bitOutcome, j, hnot, hne] at hout
    exact hout.symm
  have hqpos : 0<q := by dsimp [q]; omega
  have hfactor : q=2^t*d := (stripTwos_spec q hqpos).1
  have hdodd : d%2=1 := (stripTwos_spec q hqpos).2
  have hlowIndex : 4*2^j≤a+j+4 := firstFailIndex_low a
  have hq7 : 7≤2^t*d := by
    rw [←hfactor]
    dsimp [q]
    have hp : 1≤2^j := Nat.one_le_pow j 2 (by decide)
    omega
  have heq := CascadeResetInverse.odd_output_equation t d hdodd hq7
  have heqentry : 2*h+5=3^(t+1)*d := by rw [hentry]; exact heq
  have hband := CascadeResetInverse.odd_inverse_band a j
    (by exact hlowIndex) (by exact (firstFailIndex_spec a).2) hnot hpar
  change (6*2^j+1≤q ∧ q≤8*2^j-1) ∧
    2*q=8*2^j+a+j+5 at hband
  have htpos : 1≤t := by
    by_cases htzero : t=0
    · have hdq : q=d := by rw [hfactor,htzero]; simp
      have heq3 : 3*q=2*h+5 := by
        calc
          3*q = 3*d := by rw [hdq]
          _ = 3^(t+1)*d := by simp [htzero]
          _ = 2*h+5 := heqentry.symm
      have hgaplow : 2*2^k<q := by omega
      have hgaphigh : q<3*2^k := by omega
      exact False.elim
        (middle_quotient_gap_two_three k j q hgaplow hgaphigh hband.1)
    · omega
  have hdiv : 9∣3^(t+1)*d := by
    have hge : 2≤t+1 := by omega
    obtain ⟨r,hr⟩ := Nat.pow_dvd_pow 3 hge
    refine ⟨r*d, ?_⟩
    rw [hr]
    simp only [show (3:Nat)^2=9 by decide]
    ac_rfl
  rw [heqentry]
  exact Nat.mod_eq_zero_of_dvd hdiv

private theorem middle_low_no_parent (k h q : Nat)
    (hlow : 4*2^k≤h)
    (htop : 2*h+5<9*2^k)
    (hdiv : (2*h+5)%9≠0)
    (hgap : ∀ j, ¬(6*2^j-1≤h ∧ h≤8*2^j-3))
    (hp : ResetParent q h) : False := by
  rcases hp with ⟨j,hbj,heqj⟩ | ⟨j,t,d,hd,hbj,hout,hq⟩
  · exact hgap j hbj
  · have hpar : (q+j)%2=1 := by omega
    have hlowq : 4*2^j≤q+j+4 := by omega
    have hmaxq : q+j+5<8*2^j := by omega
    have hj : firstFailIndex q=j :=
      firstFailIndex_unique q j hmaxq (guards_from_low q j hlowq)
    have hodd : (q+firstFailIndex q)%2=1 := by
      rw [hj]
      exact hpar
    have hr : Outcome (q,0) (some h) :=
      reset_parent_sufficient q h (Or.inr ⟨j,t,d,hd,hbj,hout,hq⟩)
    have hbit : bitOutcome q=some h :=
      outcome_unique (bitOutcome_sound q) hr
    exact hdiv (middle_low_odd_output_mod_nine q h k hodd hbit hlow htop)

/-- New full no-predecessor cylinder at any dyadic scale: every h in
    [4·2^k, (9·2^k−5)/2) with 9 ∤ (2h+5) is inaccessible from the
    authentic blank first-reset height 2. This includes targets h≡2 mod3
    which survive the previous coarse odd-parent filter. -/
theorem middle_low_root_nonimage (k h : Nat)
    (hk : 3≤k)
    (hlow : 4*2^k≤h)
    (htop : 2*h+5<9*2^k)
    (hdiv : (2*h+5)%9≠0) :
    ¬ReachC (2,0) (h,0) := by
  have hmin : 4*2^k-3<h := by omega
  have hmax : h<6*2^k-1 := by omega
  have hgap : ∀ j, ¬(6*2^j-1≤h ∧ h≤8*2^j-3) := by
    intro j
    have hshift : (k+1)-1=k := by omega
    exact TerminalExit.no_even_band (k+1) j h
      (by omega) (by simpa [hshift] using hmin)
      (by simpa [hshift] using hmax)
  have hne : h≠2 := by omega
  intro hr
  have hc : ResetChain 2 h := (root_reset_chain_iff h).mp hr
  obtain ⟨q,hqc,hq⟩ := reset_chain_last hc hne
  exact middle_low_no_parent k h q hlow htop hdiv hgap hq

theorem middle_low_example_4100 :
    ¬ ReachC (2,0) (4100,0) := by
  apply middle_low_root_nonimage 10 4100
  all_goals decide

#print axioms middle_low_odd_output_mod_nine
#print axioms middle_low_root_nonimage
#print axioms middle_low_example_4100
end CascadeFastReturn
