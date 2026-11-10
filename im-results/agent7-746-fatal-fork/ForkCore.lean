import ResetChain
set_option maxHeartbeats 0

namespace BB746Fork

abbrev ResetParent := CascadeResetInverse.ResetParent

theorem even_unique (u a b : Nat)
    (ha : 6*2^a-1≤u ∧ u≤8*2^a-3)
    (hb : 6*2^b-1≤u ∧ u≤8*2^b-3) : a=b := by
  have hap : 1≤2^a := Nat.one_le_pow a 2 (by decide)
  have hbp : 1≤2^b := Nat.one_le_pow b 2 (by decide)
  by_cases he : a=b
  · exact he
  by_cases hlt : a<b
  · have hpow : 2^(a+1)≤2^b := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hpow
    omega
  · have hpow : 2^(b+1)≤2^a := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hpow
    omega

private theorem odd_unique (u a b : Nat)
    (ha : 6*2^a+1≤u ∧ u≤8*2^a-1)
    (hb : 6*2^b+1≤u ∧ u≤8*2^b-1) : a=b := by
  by_cases he : a=b
  · exact he
  by_cases hlt : a<b
  · have hpow : 2^(a+1)≤2^b := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hpow
    omega
  · have hpow : 2^(b+1)≤2^a := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hpow
    omega

private theorem quotient_gap_four_six (k j q : Nat)
    (hl : 4*2^k<q) (hh : q<6*2^k)
    (hb : 6*2^j+1≤q ∧ q≤8*2^j-1) : False := by
  by_cases he : j<k
  · have hpow : 2^(j+1)≤2^k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hpow
    omega
  · have hpow : 2^k≤2^j := Nat.pow_le_pow_right (by decide) (by omega)
    omega

private theorem quotient_gap_two_three (k j q : Nat)
    (hl : 2*2^k<q) (hh : q<3*2^k)
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

/-- Complete two-parent grammar for a narrow high target whose odd
numerator has exact 3-adic valuation three. Unlike the mod-27 image
criterion, this characterizes every incoming first reset. -/
theorem narrow_exact_two (k x h y q : Nat)
    (hk : 2≤k)
    (hhigh : 6*2^k≤x)
    (hguard : x+k+5<8*2^k)
    (hnarrow : 4*x+10<27*2^k)
    (hnot81 : (2*x+5)%81≠0)
    (heven : 2*x=8*2^k+h+k)
    (hodd : 27*(2*2^k+y+k+3)=8*(2*x+5))
    (hband : 6*2^k-1≤x ∧ x≤8*2^k-3) :
    ResetParent q x → q=h ∨ q=y := by
  intro hp
  rcases hp with ⟨j,hbj,heqj⟩ | ⟨j,t,d,hd,hbj,hout,hq⟩
  · have hjk : j=k := even_unique x j k hbj hband
    left
    rw [hjk] at heqj
    omega
  · by_cases ht0 : t=0
    · subst t
      have hN : 2*x+5=3*d := by simpa using hout
      have hgaplo : 4*2^k<d := by omega
      have hgaphigh : d<6*2^k := by omega
      have hb' : 6*2^j+1≤d ∧ d≤8*2^j-1 := by simpa using hbj
      exact False.elim (quotient_gap_four_six k j d hgaplo hgaphigh hb')
    · by_cases ht1 : t=1
      · subst t
        have hN : 2*x+5=9*d := by simpa using hout
        have hq' : 2*2^k<2*d ∧ 2*d<3*2^k := by omega
        have hb' : 6*2^j+1≤2*d ∧ 2*d≤8*2^j-1 := by simpa using hbj
        exact False.elim (quotient_gap_two_three k j (2*d) hq'.1 hq'.2 hb')
      · have htbound : t≤2 := by
          by_cases hge : 3≤t
          · have he : t+1=4+(t-3) := by omega
            have hpow : 3^(t+1)%81=0 := by rw [he,Nat.pow_add]; simp
            have hzero : (2*x+5)%81=0 := by rw [hout,Nat.mul_mod,hpow]; simp
            exact False.elim (hnot81 hzero)
          · omega
        have ht : t=2 := by omega
        subst t
        have hN : 2*x+5=27*d := by simpa using hout
        have hk' : (k-2)+2=k := by omega
        have hpow : 2^k=4*2^(k-2) := by
          calc
            2^k = 2^((k-2)+2) := by rw [hk']
            _ = 4*2^(k-2) := by rw [Nat.pow_add]; omega
        have hp' : 1≤2^(k-2) := Nat.one_le_pow _ _ (by decide)
        have hb' : 6*2^(k-2)+1≤4*d ∧ 4*d≤8*2^(k-2)-1 := by
          constructor <;> omega
        have hj : j=k-2 := odd_unique (4*d) j (k-2)
          (by simpa using hbj) hb'
        right
        rw [hj] at hq
        have hlinear : 27*(2*2^k+y+k+3)=27*(8*2^(k-2)+y+(k-2)+5) := by rw [hpow]; omega
        have hq' : 2*(4*d)=8*2^(k-2)+q+(k-2)+5 := by simpa using hq
        omega

#print axioms narrow_exact_two
end BB746Fork
