import SweepNoEvenEvenFatal

/-- A short positive offset after a large dyadic power cannot be a
    power-of-two multiple of any small positive residual. -/
theorem no_small_dyadic_factor (k c m d : Nat)
    (hk : 8≤k) (hcpos : 0<c) (hcupper : c≤2*k+4)
    (hdpos : 0<d) (hdupper : d≤4*k+10)
    (heq : 2^(k+2)+c=2^m*d) : False := by
  have hp := dyadic_gap_k k hk
  have hsmall : c<2^(k+1) := by
    have hone : 1≤2*k+5 := by omega
    have hb : 2*k+4≤(2*k+4)*(2*k+5) := by
      have hp2 := Nat.mul_le_mul_left (2*k+4) hone
      simpa using hp2
    omega
  have hpower : 2^(k+3)=2*2^(k+2) := by
    rw [show k+3=(k+2)+1 by omega, Nat.pow_succ]
    omega
  have hpower2 : 2^(k+2)=2*2^(k+1) := by
    rw [show k+2=(k+1)+1 by omega,Nat.pow_succ]
    omega
  have hsum : 2^(k+2)+c<2^(k+3) := by omega
  have hmule : 2^m≤2^m*d := by
    have hh := Nat.mul_le_mul_left (2^m) (by omega : 1≤d)
    simpa using hh
  have hpwrlt : 2^m<2^(k+3) := by omega
  have hm : m≤k+2 := by
    have hlt : m<k+3 := (Nat.pow_lt_pow_iff_right (by decide)).1 hpwrlt
    omega
  have hdiv : 2^m∣2^(k+2) := Nat.pow_dvd_pow 2 hm
  have hdivsum : 2^m∣2^(k+2)+c := ⟨d,heq⟩
  have hdivc : 2^m∣c := (Nat.dvd_add_iff_right hdiv).2 hdivsum
  have hprod : (2*k+4)*(4*k+10)=2*((2*k+4)*(2*k+5)) := by
    have he : 4*k+10=2*(2*k+5) := by omega
    rw [he]
    ac_rfl
  have hdom : (2*k+4)*(4*k+10)<2^(k+2) := by
    rw [hprod,hpower2]
    omega
  have hpowgt : c<2^m := by
    by_cases hh : c<2^m
    · exact hh
    have hmprod : 2^m*d≤(2*k+4)*(4*k+10) := by
      have hh1 := Nat.mul_le_mul (by omega : 2^m≤2*k+4) hdupper
      simpa using hh1
    omega
  have hpowle : 2^m≤c := Nat.le_of_dvd hcpos hdivc
  omega

namespace CascadeFastReturn
open CascadeBitSweep

/-- After a successful even level-j exit (j≥7), every later genuine level
    exit from level j+1, after an arbitrary number of same-level resets, must
    be odd if it succeeds. Two consecutive successful even level exits are
    impossible at all high levels, regardless of the destination's fatality. -/
theorem no_consecutive_even_level_exits (j a x z v m : Nat)
    (hj : 7≤j)
    (ha : firstFailIndex a=j)
    (hax : bitOutcome a=some x)
    (haeven : (a+j)%2=0)
    (hx : firstFailIndex x=j+1)
    (hpath : SameLevelPath (j+1) x z m)
    (hz : bitOutcome z=some v)
    (hzeven : (z+(j+1))%2=0)
    (hv : firstFailIndex v=j+2) : False := by
  obtain ⟨c,hclo,hchi,hband⟩ := even_level_entry_deficit_band j a x ha hax haeven hx
  have hk : firstFailIndex z=j+1 := same_level_path_last (j+1) x z m hpath
  have hnext : firstFailIndex v=(j+1)+1 := by omega
  have hsmall := (even_edge_advance_iff_small_deficit z v hz (by rw [hk]; exact hzeven)).1
    (by rw [hk]; exact hnext)
  rw [hk] at hsmall
  have hDpos := level_deficit_min z
  rw [hk] at hDpos
  have hfactor := same_level_path_exact_deficit (j+1) x z m hpath
  have hd : 0<deficitAt (j+1) z := by omega
  have hparity := deficit_parity (j+1) z hk
  have hdeven : (deficitAt (j+1) z)%2=0 := by
    rw [←hparity]
    exact hzeven
  have hdupper : deficitAt (j+1) z≤4*(j+1)+10 := by omega
  have hkmin : 8≤j+1 := by omega
  have hcpos : 0<c := by omega
  have hcupper : c≤2*(j+1)+4 := by omega
  have hpoweq : 2^((j+1)+2)+c=2^m*deficitAt (j+1) z := by
    rw [show (j+1)+2=j+3 by omega]
    rw [←hband]
    exact hfactor
  exact no_small_dyadic_factor (j+1) c m (deficitAt (j+1) z)
    hkmin hcpos hcupper hd hdupper hpoweq

#print axioms no_small_dyadic_factor
#print axioms no_consecutive_even_level_exits
end CascadeFastReturn
