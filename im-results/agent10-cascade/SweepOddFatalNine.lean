import SweepOddFatalDepth

namespace CascadeFastReturn
open CascadeBitSweep

private theorem gap_no_odd_q (k j q : Nat)
    (hl : 4*2^k < q) (hh : q < 6*2^k)
    (hb : 6*2^j+1≤q ∧ q≤8*2^j-1) : False := by
  by_cases he : j<k
  · have hpow : 2^(j+1)≤2^k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hpow
    omega
  · have hpow : 2^k≤2^j := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- At any level k, an odd reset landing in the top quarter of the level
    (height >= 6*2^k) is a 3²-divisible odd source image. The t=0 odd
    inverse would place q strictly between 4*2^k and 6*2^k, where the complete
    source odd inverse band has no member. -/
theorem high_odd_bit_output_mod_nine (a entry k : Nat)
    (hodd : (a+firstFailIndex a)%2=1)
    (hout : bitOutcome a=some entry)
    (hk : firstFailIndex entry=k)
    (hhigh : 6*2^k≤entry) :
    (2*entry+5)%9=0 := by
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
  have htpos : 1≤t := by
    by_cases htzero : t=0
    · have hdq : q=d := by rw [hfactor,htzero]; simp
      have heq3 : 2*entry+5=3*q := by
        rw [heqentry,htzero]
        rw [hdq]
      have hentryhigh := (firstFailIndex_spec entry).2
      rw [hk] at hentryhigh
      have hgaplow : 4*2^k<q := by omega
      have hgaphigh : q<6*2^k := by omega
      exact False.elim (gap_no_odd_q k j q hgaplow hgaphigh hband.1)
    · omega
  have hdiv9 : 9∣3^(t+1)*d := by
    have hge : 2≤t+1 := by omega
    obtain ⟨r,hr⟩ := Nat.pow_dvd_pow 3 hge
    refine ⟨r*d, ?_⟩
    rw [hr]
    simp only [show (3:Nat)^2=9 by decide]
    ac_rfl
  rw [heqentry]
  exact Nat.mod_eq_zero_of_dvd hdiv9

private theorem high_odd_fatal_mod_nine_arithmetic (k entry m : Nat)
    (hdiv : (2*entry+5)%9=0)
    (hdef : entry+2^m*(4*k+10)=8*2^k+k) :
    (16*2^k+2*k+5)%9=(2^(m+1)*(4*k+10))%9 := by
  have hpow : 2^(m+1)=2*2^m := by rw [Nat.pow_succ]; omega
  have hscale : (2*2^m)*(4*k+10)=2*(2^m*(4*k+10)) := by ac_rfl
  have hp : 16*2^k=2*(8*2^k) := by omega
  have heq : 16*2^k+2*k+5=(2*entry+5)+2^(m+1)*(4*k+10) := by
    rw [hpow, hscale, hp]
    omega
  rw [heq, Nat.add_mod, hdiv]
  simp

/-- A source odd-entry and adjacent even-fatal history with entry height in
    the top quarter of its level must satisfy this exact mod-9 gate. It cuts
    all but one odd m residue class modulo 6 at each eligible fatal level. -/
theorem high_odd_entry_adjacent_fatal_mod_nine (k a entry z v m : Nat)
    (haodd : (a+firstFailIndex a)%2=1)
    (ha : bitOutcome a=some entry)
    (hk : firstFailIndex entry=k)
    (hentryhigh : 6*2^k≤entry)
    (hp : SameLevelPath k entry z m)
    (hz : bitOutcome z=some v)
    (hu : firstFailIndex v=k+1)
    (hf : fatalAt v) :
    (16*2^k+2*k+5)%9=(2^(m+1)*(4*k+10))%9 := by
  have hdiv := high_odd_bit_output_mod_nine a entry k haodd ha hk hentryhigh
  have hdef := adjacent_fatal_after_same_level_path k entry z v m hp hz hu hf
  have hbound := (firstFailIndex_spec entry).2
  rw [hk] at hbound
  have heq : entry+2^m*(4*k+10)=8*2^k+k := by
    dsimp [deficitAt] at hdef
    omega
  exact high_odd_fatal_mod_nine_arithmetic k entry m hdiv heq

#print axioms high_odd_bit_output_mod_nine
#print axioms high_odd_entry_adjacent_fatal_mod_nine
end CascadeFastReturn
