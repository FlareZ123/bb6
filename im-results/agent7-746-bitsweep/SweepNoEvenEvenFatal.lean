import SweepQuadraticRank

/-- A dyadic power exceeds the quadratic polynomial once its index is eight. -/
private theorem double_poly (a : Nat) :
    (a+22)*(a+23) ≤ 2*((a+20)*(a+21)) := by
  have he : 2*((a+20)*(a+21)) =
      (a+22)*(a+23)+(a*a+37*a+334) := by
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  omega

private theorem gap_aux (n : Nat) :
    (2*n+20)*(2*n+21) < 2^(n+9) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have he : 2^(n+1+9)=2*2^(n+9) := by
      rw [show n+1+9=n+9+1 by omega,Nat.pow_succ]
      omega
    rw [he]
    have hp := double_poly (2*n)
    have hdeq : (2*(n+1)+20)*(2*(n+1)+21)=(2*n+22)*(2*n+23) := by
      congr 1 <;> omega
    rw [hdeq]
    omega

private theorem gap (k : Nat) (hk : 8≤k) :
    (2*k+4)*(2*k+5) < 2^(k+1) := by
  have hn := gap_aux (k-8)
  have he : k-8+8=k := by omega
  simpa [show 2*k+4=2*(k-8)+20 by omega,
    show 2*k+5=2*(k-8)+21 by omega,
    show k+1=(k-8)+9 by omega] using hn

/-- A power-of-two multiple of 4k+10 cannot lie in the short band
    2^(k+2)+[1,2k+4] for any k at least eight. -/
private theorem no_dyadic_eq (k c m : Nat) (hk : 8≤k)
    (hcpos : 0<c) (hcupper : c≤2*k+4)
    (heq : 2^(k+2)+c=2^m*(4*k+10)) : False := by
  have hp := gap k hk
  have hsmall : c<2^(k+1) := by
    have hone : 1≤2*k+5 := by omega
    have hb : 2*k+4≤(2*k+4)*(2*k+5) := by
      have hp2 := Nat.mul_le_mul_left (2*k+4) hone
      simpa using hp2
    omega
  have hpower : 2^(k+3)=2*(2^(k+2)) := by
    rw [show k+3=(k+2)+1 by omega, Nat.pow_succ]
    omega
  have hpower2 : 2^(k+2)=2*(2^(k+1)) := by
    rw [show k+2=(k+1)+1 by omega,Nat.pow_succ]
    omega
  have hsum : 2^(k+2)+c<2^(k+3) := by omega
  have hfactor : 1≤4*k+10 := by omega
  have hmule : 2^m≤2^m*(4*k+10) := by
    have h := Nat.mul_le_mul_left (2^m) hfactor
    simpa using h
  have hpwrlt : 2^m<2^(k+3) := by omega
  have hm : m≤k+2 := by
    have hlt : m<k+3 := (Nat.pow_lt_pow_iff_right (by decide)).1 hpwrlt
    omega
  have hdiv : 2^m∣2^(k+2) := Nat.pow_dvd_pow 2 hm
  have hdivsum : 2^m∣2^(k+2)+c := ⟨4*k+10,heq⟩
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
    have hcg : 2^m≤c := by omega
    have hmprod : 2^m*(4*k+10)≤(2*k+4)*(4*k+10) := by
      have hp0 := Nat.mul_le_mul_right (4*k+10) (by omega : 2^m≤2*k+4)
      simpa using hp0
    omega
  have hpowle : 2^m≤c := Nat.le_of_dvd hcpos hdivc
  omega

/-- Dyadic-vs-polynomial gap for all k at least eight. -/
theorem dyadic_gap_k (k : Nat) (hk : 8≤k) :
    (2*k+4)*(2*k+5) < 2^(k+1) := gap k hk

namespace CascadeFastReturn
open CascadeBitSweep

/-- Every genuine even level-j exit enters level j+1 with a deficit of
    2^(j+3)+c, where c is positive and at most 2j+6. -/
theorem even_level_entry_deficit_band (j a x : Nat)
    (ha : firstFailIndex a=j)
    (hax : bitOutcome a=some x)
    (heven : (a+j)%2=0)
    (hx : firstFailIndex x=j+1) :
    ∃c, j+4≤c ∧ c≤2*j+6 ∧
      deficitAt (j+1) x=2^(j+3)+c := by
  have hmin := level_deficit_min a
  rw [ha] at hmin
  have hsmall := (even_edge_advance_iff_small_deficit a x hax (by rw [ha];exact heven)).1
    (by rw [ha];exact hx)
  rw [ha] at hsmall
  have hhalve := bitOutcome_even_deficit_halves a j x ha heven hax
  have hxupper := even_edge_below_eight a x hax (by rw [ha]; exact heven)
  rw [ha] at hxupper
  let e := deficitAt j x
  have helo : j+3≤e := by
    change 2*j+6≤deficitAt j a at hmin
    change deficitAt j a=2*e at hhalve
    omega
  have hehi : e≤2*j+5 := by
    change deficitAt j a<4*j+12 at hsmall
    change deficitAt j a=2*e at hhalve
    omega
  have hp : 2^(j+1)=2*2^j := by rw [Nat.pow_succ]; omega
  have hp2 : 2^(j+3)=8*2^j := by rw [Nat.pow_add]; simp [Nat.mul_comm]
  have hlink : deficitAt (j+1) x=8*2^j+1+e := by
    dsimp [deficitAt,e]
    rw [hp]
    omega
  refine ⟨e+1,by omega,by omega,?_⟩
  rw [hlink,hp2]
  omega

/-- No consecutive even dyadic-level exits can reach a fatal state at level
    j+2≥9, irrespective of the number of genuine same-level resets between
    the exits. A fatal entry at such a height requires an earlier odd exit
    or a different level-history shape. -/
theorem no_even_then_even_fatal (j a x z v m : Nat)
    (hj : 7≤j)
    (ha : firstFailIndex a=j)
    (hax : bitOutcome a=some x)
    (heven : (a+j)%2=0)
    (hx : firstFailIndex x=j+1)
    (hpath : SameLevelPath (j+1) x z m)
    (hz : bitOutcome z=some v)
    (hv : firstFailIndex v=j+2)
    (hf : fatalAt v) : False := by
  obtain ⟨c,hclo,hchi,hband⟩ := even_level_entry_deficit_band j a x ha hax heven hx
  have hnext : firstFailIndex v=(j+1)+1 := by omega
  have htarget := adjacent_fatal_after_same_level_path (j+1) x z v m hpath hz hnext hf
  have hh : 8≤j+1 := by omega
  have hcpos : 0<c := by omega
  have hcup : c≤2*(j+1)+4 := by omega
  have hpoweq : 2^((j+1)+2)+c=2^m*(4*(j+1)+10) := by
    rw [show (j+1)+2=j+3 by omega]
    rw [←hband]
    simpa [show (j+1)+1=j+2 by omega] using htarget
  exact no_dyadic_eq (j+1) c m hh hcpos hcup hpoweq

#print axioms even_level_entry_deficit_band
#print axioms no_even_then_even_fatal
end CascadeFastReturn
