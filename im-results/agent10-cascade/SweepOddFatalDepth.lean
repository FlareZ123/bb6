import SweepAlternatingMacro

namespace CascadeFastReturn
open CascadeBitSweep

private theorem two_pow_mod_three (n : Nat) :
    (2^n)%3 = if n%2=0 then 1 else 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    by_cases he : n%2=0
    · have hmod : (n+1)%2=1 := by omega
      simp [he, hmod] at ih ⊢
      omega
    · have hn : n%2=1 := by omega
      have hmod : (n+1)%2=0 := by omega
      simp [hn, hmod] at ih ⊢
      omega

/-- Exact source odd first-return outputs lie in the residue 2u+5=0 (mod 3). -/
theorem odd_bit_output_mod_three (a entry : Nat)
    (hodd : (a+firstFailIndex a)%2=1)
    (hout : bitOutcome a=some entry) :
    (2*entry+5)%3=0 := by
  let k := firstFailIndex a
  let q := 4*2^k+(a+k)/2+3
  let t := (stripTwos q).1
  let d := (stripTwos q).2
  have hnot : a+k+4≠4*2^k := by
    intro hf
    have hnone : bitOutcome a=none := by simp [bitOutcome, k, hf]
    rw [hnone] at hout
    cases hout
  have hpar : (a+k)%2≠0 := by omega
  have hentry : entry=(3^(t+1)*d-5)/2 := by
    simp [bitOutcome, k, hnot, hpar] at hout
    exact hout.symm
  have hqpos : 0<q := by dsimp [q]; omega
  have hfactor : q=2^t*d := (stripTwos_spec q hqpos).1
  have hdodd : d%2=1 := (stripTwos_spec q hqpos).2
  have hlow := firstFailIndex_low a
  have hq7 : 7≤2^t*d := by
    rw [←hfactor]
    dsimp [q]
    change 4*2^k ≤ a+k+4 at hlow
    omega
  have heq := CascadeResetInverse.odd_output_equation t d hdodd hq7
  have hthree : 3∣3^(t+1)*d := by
    rw [Nat.pow_succ]
    refine ⟨3^t*d, ?_⟩
    ac_rfl
  rw [hentry, heq]
  exact Nat.mod_eq_zero_of_dvd hthree

private theorem odd_entry_fatal_even_depth_arithmetic (k entry m : Nat)
    (hdiv : (2*entry+5)%3=0)
    (hdef : entry+2^m*(4*k+10)=8*2^k+k) :
    m%2=1 := by
  by_cases heven : m%2=0
  · have hpow : (2^m)%3=1 := by
      rw [two_pow_mod_three m]
      simp [heven]
    have hpm : (2^k)%3≠0 := by
      rw [two_pow_mod_three k]
      split <;> omega
    have hem : (2^m*(4*k+10))%3=(4*k+10)%3 := by
      rw [Nat.mul_mod, hpow]
      omega
    omega
  · omega

/-- If an odd source first-reset edge enters level k, then m authentic
    same-level first resets followed by a successful adjacent-level even exit
    into the fatal threshold of level k+1 require m odd. This excludes every
    even-depth such predecessor history, for all k and all source heights. -/
theorem odd_entry_adjacent_fatal_depth_odd (k a entry z v m : Nat)
    (haodd : (a+firstFailIndex a)%2=1)
    (ha : bitOutcome a=some entry)
    (hk : firstFailIndex entry=k)
    (hp : SameLevelPath k entry z m)
    (hz : bitOutcome z=some v)
    (hu : firstFailIndex v=k+1)
    (hf : fatalAt v) : m%2=1 := by
  have hdiv := odd_bit_output_mod_three a entry haodd ha
  have hdef := adjacent_fatal_after_same_level_path k entry z v m hp hz hu hf
  have hbound := (firstFailIndex_spec entry).2
  rw [hk] at hbound
  have heq : entry+2^m*(4*k+10)=8*2^k+k := by
    dsimp [deficitAt] at hdef
    omega
  exact odd_entry_fatal_even_depth_arithmetic k entry m hdiv heq

#print axioms odd_bit_output_mod_three
#print axioms odd_entry_adjacent_fatal_depth_odd
end CascadeFastReturn
