import ForkRoot
set_option maxHeartbeats 0
namespace BB746Fork

private theorem odd_gap_one_onehalf (k j q : Nat)
    (hl : 2^k<q) (hh : 2*q<3*2^k)
    (hb : 6*2^j+1≤q ∧ q≤8*2^j-1) : False := by
  by_cases he : j+3≤k
  · have hp : 2^(j+3)≤2^k := Nat.pow_le_pow_right (by decide) he
    have heq : 2^(j+3)=8*2^j := by rw [Nat.pow_add]; omega
    rw [heq] at hp
    omega
  · have hpow : 2^k≤2^(j+2) := Nat.pow_le_pow_right (by decide) (by omega)
    have heq : 2^(j+2)=4*2^j := by rw [Nat.pow_add]; omega
    rw [heq] at hpow
    omega

private theorem quotient_gap_two_three_local (k j q : Nat)
    (hl : 2*2^k < q) (hh : q < 3*2^k)
    (hb : 6*2^j+1≤q ∧ q≤8*2^j-1) : False := by
  by_cases he : j+2≤k
  · have hpow : 2^(j+2)≤2^k := Nat.pow_le_pow_right (by decide) he
    have heq : 2^(j+2)=4*2^j := by rw [Nat.pow_add]; omega
    rw [heq] at hpow
    omega
  · have hkj : k≤j+1 := by omega
    have hpow : 2^k≤2^(j+1) := Nat.pow_le_pow_right (by decide) hkj
    rw [Nat.pow_succ] at hpow
    omega

private theorem odd_unique_local (q k j : Nat)
    (h1 : 6*2^k+1≤q ∧ q≤8*2^k-1)
    (h2 : 6*2^j+1≤q ∧ q≤8*2^j-1) : k=j := by
  by_cases eq : k=j
  · exact eq
  by_cases hlt : k<j
  · have hp : 2^(k+1)≤2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hp
    omega
  · have hp : 2^(j+1)≤2^k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hp
    omega

/-- Stronger middle-low one-odd-parent theorem: exact 3-adic valuation
three of the numerator is permitted. The valuation-two quotient falls
inside a dyadic gap (P,3P/2), instead of requiring a mod-27 obstruction. -/
theorem middle_low_unique_odd_even_if_27 (k h a q : Nat)
    (hk : 4≤k)
    (hlo : 4*2^k≤h)
    (htop : 2*h+5<9*2^k)
    (hdiv : (2*h+5)%9=0)
    (hno81 : (2*h+5)%81≠0)
    (ha : 4*((2*h+5)/9)=8*2^(k-2)+a+(k-2)+5)
    (hq : ResetParent q h) : q=a := by
  have hpow : 2^k=4*2^(k-2) := by
    have he : k=(k-2)+2 := by omega
    calc
      2^k = 2^((k-2)+2) := congrArg (fun j : Nat => 2^j) he
      _ = 4*2^(k-2) := by rw [Nat.pow_add]; omega
  have hgaplo : 4*2^k-3<h := by omega
  have hgaphigh : h<6*2^k-1 := by omega
  rcases hq with ⟨j,hbj,heq⟩ | ⟨j,t,d,hdodd,hbj,hout,heq⟩
  · by_cases hl : j<k
    · have hp : 2^(j+1)≤2^k := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.pow_succ] at hp
      omega
    · have hp : 2^k≤2^j := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  · by_cases ht0 : t=0
    · subst t
      have hnum : 2*h+5=3*d := by simpa using hout
      have hlo' : 2*2^k<d := by omega
      have hhi' : d<3*2^k := by omega
      exact False.elim (quotient_gap_two_three_local k j d hlo' hhi'
        (by simpa using hbj))
    · by_cases ht1 : t=1
      · subst t
        have hnum : 2*h+5=9*d := by simpa using hout
        have hd' : d=(2*h+5)/9 := by omega
        have hp1 : 1≤2^(k-2) := Nat.one_le_pow _ _ (by decide)
        have hband : 6*2^(k-2)+1≤2*d ∧ 2*d≤8*2^(k-2)-1 := by
          constructor <;> omega
        have hj : j=k-2 := odd_unique_local (2*d) j (k-2)
          (by simpa using hbj) hband
        rw [hj] at heq
        have ha' : 4*d=8*2^(k-2)+a+(k-2)+5 := by simpa [hd'] using ha
        omega
      · by_cases ht2 : t=2
        · subst t
          have hnum : 2*h+5=27*d := by simpa using hout
          have hlo' : 2^k<4*d := by omega
          have hhi' : 2*(4*d)<3*2^k := by omega
          exact False.elim (odd_gap_one_onehalf k j (4*d) hlo' hhi'
            (by simpa using hbj))
        · have ht3 : 3≤t := by omega
          have he : t+1=4+(t-3) := by omega
          have hpow81 : 3^(t+1)%81=0 := by rw [he,Nat.pow_add]; simp
          have hzero : (2*h+5)%81=0 := by rw [hout,Nat.mul_mod,hpow81]; simp
          exact False.elim (hno81 hzero)

#print axioms middle_low_unique_odd_even_if_27
end BB746Fork
