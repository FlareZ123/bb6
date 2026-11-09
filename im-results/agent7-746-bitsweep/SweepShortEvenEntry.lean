import SweepOddAfterEven

namespace CascadeFastReturn
open CascadeBitSweep

/-- Every genuine same-level block immediately after a high successful even
    level entry has length logarithmic in the *level index* (not in the
    exponentially larger tape height). For all j≥7, m≤log₂(2(j+1)+4). -/
theorem even_entry_short_same_level_path (j a x z m : Nat)
    (hj : 7≤j)
    (ha : firstFailIndex a=j)
    (hax : bitOutcome a=some x)
    (haeven : (a+j)%2=0)
    (hx : firstFailIndex x=j+1)
    (hpath : SameLevelPath (j+1) x z m) :
    m≤Nat.log2 (2*(j+1)+4) := by
  let k := j+1
  obtain ⟨c,hclo,hchi,hband⟩ := even_level_entry_deficit_band j a x ha hax haeven hx
  have hfactor := same_level_path_exact_deficit k x z m hpath
  have hk : firstFailIndex z=k := same_level_path_last k x z m hpath
  have hdmin := level_deficit_min z
  rw [hk] at hdmin
  have hdpos : 0<deficitAt k z := by omega
  have hp := dyadic_gap_k k (by omega : 8≤k)
  have hsmall : c<2^(k+1) := by
    have hone : 1≤2*k+5 := by omega
    have hb : 2*k+4≤(2*k+4)*(2*k+5) := by
      have hp2 := Nat.mul_le_mul_left (2*k+4) hone
      simpa using hp2
    omega
  have hp2 : 2^(k+2)=2*2^(k+1) := by
    rw [show k+2=k+1+1 by omega, Nat.pow_succ]
    omega
  have hp3 : 2^(k+3)=2*2^(k+2) := by
    rw [show k+3=k+2+1 by omega, Nat.pow_succ]
    omega
  have hfac : 2^(k+2)+c=2^m*deficitAt k z := by
    rw [show k+2=j+3 by omega, ←hband]
    exact hfactor
  have hsum : 2^(k+2)+c<2^(k+3) := by omega
  have hmule : 2^m≤2^m*deficitAt k z := by
    have hmul := Nat.mul_le_mul_left (2^m) (by omega : 1≤deficitAt k z)
    simpa using hmul
  have hpowlt : 2^m<2^(k+3) := by omega
  have hm : m≤k+2 := by
    have hh : m<k+3 := (Nat.pow_lt_pow_iff_right (by decide)).1 hpowlt
    omega
  have hdiv : 2^m∣2^(k+2) := Nat.pow_dvd_pow 2 hm
  have hdivsum : 2^m∣2^(k+2)+c := ⟨deficitAt k z,hfac⟩
  have hdivc : 2^m∣c := (Nat.dvd_add_iff_right hdiv).2 hdivsum
  have hcpos : 0<c := by omega
  have hp_le_c : 2^m≤c := Nat.le_of_dvd hcpos hdivc
  have hp_le_upper : 2^m≤2*k+4 := by omega
  exact (Nat.le_log2 (by omega : 2*k+4 ≠ 0)).2 hp_le_upper

#print axioms even_entry_short_same_level_path
end CascadeFastReturn
