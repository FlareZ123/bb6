import SweepOddFatalResidue
import SweepOddFatal27Arithmetic

namespace CascadeFastReturn
open CascadeBitSweep CascadeFatalDepth27

private theorem odd_quotient_gap_four_six (k j q : Nat)
    (hl : 4*2^k < q) (hh : q < 6*2^k)
    (hb : 6*2^j+1≤q ∧ q≤8*2^j-1) : False := by
  by_cases he : j<k
  · have hpow : 2^(j+1)≤2^k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hpow
    omega
  · have hpow : 2^k≤2^j := Nat.pow_le_pow_right (by decide) (by omega)
    omega

private theorem odd_quotient_gap_two_three (k j q : Nat)
    (hl : 2*2^k < q) (hh : q < 3*2^k)
    (hb : 6*2^j+1≤q ∧ q≤8*2^j-1) : False := by
  by_cases he : j+2≤k
  · have hpow : 2^(j+2)≤2^k := Nat.pow_le_pow_right (by decide) he
    have heq : 2^(j+2)=4*2^j := by
      rw [show j+2=(j+1)+1 by omega, Nat.pow_succ, Nat.pow_succ]
      omega
    rw [heq] at hpow
    omega
  · have hkj : k≤j+1 := by omega
    have hpow : 2^k≤2^(j+1) := Nat.pow_le_pow_right (by decide) hkj
    rw [Nat.pow_succ] at hpow
    omega

/-- An odd source first reset into the band 6·2^k ≤ e and
    4e+10 < 27·2^k must have valuation t≥2.
    The t=0 quotient lies in the forbidden (4p,6p) gap,
    while t=1 lies in the forbidden (2p,3p) gap.
    Hence 27 divides the exact source output offset 2e+5. -/
theorem narrow_high_odd_output_mod_twentyseven (a entry k : Nat)
    (hodd : (a+firstFailIndex a)%2=1)
    (hout : bitOutcome a=some entry)
    (hk : firstFailIndex entry=k)
    (hhigh : 6*2^k≤entry)
    (htop : 4*entry+10<27*2^k) :
    (2*entry+5)%27=0 := by
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
  have hentry : entry=(3^(t+1)*d-5)/2 := by
    have hne : (a+j)%2≠0 := by omega
    simp [bitOutcome, j, hnot, hne] at hout
    exact hout.symm
  have hqpos : 0<q := by dsimp [q]; omega
  have hfactor : q=2^t*d := (stripTwos_spec q hqpos).1
  have hdodd : d%2=1 := (stripTwos_spec q hqpos).2
  have hlow : 4*2^j≤a+j+4 := firstFailIndex_low a
  have hq7 : 7≤2^t*d := by
    rw [←hfactor]
    dsimp [q]
    have hp : 1≤2^j := Nat.one_le_pow j 2 (by decide)
    omega
  have heq := CascadeResetInverse.odd_output_equation t d hdodd hq7
  have heqentry : 2*entry+5=3^(t+1)*d := by rw [hentry]; exact heq
  have hband := CascadeResetInverse.odd_inverse_band a j (by exact hlow)
    (by exact (firstFailIndex_spec a).2) hnot hpar
  change (6*2^j+1≤q ∧ q≤8*2^j-1) ∧ 2*q=8*2^j+a+j+5 at hband
  have htpos : 2≤t := by
    by_cases htzero : t=0
    · have hdq : q=d := by rw [hfactor,htzero]; simp
      have heq3 : 3*q=2*entry+5 := by
        calc
          3*q = 3*d := by rw [hdq]
          _ = 3^(t+1)*d := by simp [htzero]
          _ = 2*entry+5 := heqentry.symm
      have hentryhigh := (firstFailIndex_spec entry).2
      rw [hk] at hentryhigh
      have hgaplow : 4*2^k<q := by omega
      have hgaphigh : q<6*2^k := by omega
      exact False.elim (odd_quotient_gap_four_six k j q hgaplow hgaphigh hband.1)
    · by_cases htone : t=1
      · have hdq : q=2*d := by rw [hfactor,htone]; simp
        have heq9 : 2*entry+5=9*d := by
          rw [heqentry,htone]
          norm_num
        have heq9q : 9*q=4*entry+10 := by omega
        have hgaplow : 2*2^k<q := by omega
        have hgaphigh : q<3*2^k := by omega
        exact False.elim (odd_quotient_gap_two_three k j q hgaplow hgaphigh hband.1)
      · omega
  have hdiv : 27∣3^(t+1)*d := by
    have hge : 3≤t+1 := by omega
    obtain ⟨r,hr⟩ := Nat.pow_dvd_pow 3 hge
    refine ⟨r*d, ?_⟩
    rw [hr]
    simp only [show (3:Nat)^3=27 by decide]
    ac_rfl
  rw [heqentry]
  exact Nat.mod_eq_zero_of_dvd hdiv

private theorem narrow_fatal_mod27_arithmetic (k entry m : Nat)
    (hdiv : (2*entry+5)%27=0)
    (hdef : entry+2^m*(4*k+10)=8*2^k+k) :
    (16*2^k+2*k+5)%27=(2^(m+1)*(4*k+10))%27 := by
  have hpow : 2^(m+1)=2*2^m := by rw [Nat.pow_succ]; omega
  have hscale : (2*2^m)*(4*k+10)=2*(2^m*(4*k+10)) := by ac_rfl
  have hp : 16*2^k=2*(8*2^k) := by omega
  have heq : 16*2^k+2*k+5=(2*entry+5)+2^(m+1)*(4*k+10) := by
    rw [hpow, hscale, hp]
    omega
  rw [heq, Nat.add_mod, hdiv]
  simp

/-- For an authentic odd entry followed by m genuine same-level resets
    and one adjacent even exit to fatal, the narrow high-entry interval
    yields one exact m mod18 class for each source level k mod54. -/
theorem narrow_odd_entry_adjacent_fatal_depth_27 (k a entry z v m : Nat)
    (haodd : (a+firstFailIndex a)%2=1)
    (ha : bitOutcome a=some entry)
    (hk : firstFailIndex entry=k)
    (hhigh : 6*2^k≤entry)
    (htop : 4*entry+10<27*2^k)
    (hp : SameLevelPath k entry z m)
    (hz : bitOutcome z=some v)
    (hu : firstFailIndex v=k+1)
    (hf : fatalAt v) :
    m%18=depth27 (k%54) := by
  have hdiv := narrow_high_odd_output_mod_twentyseven a entry k
    haodd ha hk hhigh htop
  have hdef := adjacent_fatal_after_same_level_path k entry z v m hp hz hu hf
  have hbound := (firstFailIndex_spec entry).2
  rw [hk] at hbound
  have heq : entry+2^m*(4*k+10)=8*2^k+k := by
    dsimp [deficitAt] at hdef
    omega
  have hsector := odd_entry_adjacent_fatal_level_sector k a entry z v m
    haodd ha hk hp hz hu hf
  exact fatal_depth_mod27 k m hsector
    (narrow_fatal_mod27_arithmetic k entry m hdiv heq)

#print axioms narrow_high_odd_output_mod_twentyseven
#print axioms narrow_odd_entry_adjacent_fatal_depth_27
end CascadeFastReturn
