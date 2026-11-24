import Std

/-! Arithmetic refinement of the critical P1 early-extinction argument.
The delicate even-input depth is one, not the deeper inverse branches. -/
namespace BB6.Agent45CarryWide

theorem scaled_left_strict (n m w : Nat) (hm : m ≤ n)
    (h : 6*2^n < 2^m*w) : 6*2^(n-m) < w := by
  have he : (2:Nat)^m * 2^(n-m)=2^n := by
    rw [← Nat.pow_add]
    congr 1
    omega
  by_cases hgood : 6*2^(n-m) < w
  · exact hgood
  · have hh := Nat.mul_le_mul_left (2^m) (show w ≤ 6*2^(n-m) by omega)
    have hx : (2:Nat)^m*(6*2^(n-m))=6*2^n := by rw [← he]; ac_rfl
    omega

/-- At depth one the exact gap is `b/4 - (n+m)`. At every greater
    depth the additional factor of two gives a uniform exponential gap. -/
theorem even_gap (n K b d m t k c : Nat)
    (hKn : K≤n) (hcost : m+t<K)
    (hmargin : n+K < 12*2^(n-K))
    (hb4 : b%4=0) (hd : d%2=1) (hc : c%2=0)
    (hleft : 6*2^(n-m)<(b+12)/2)
    (hmass : b+d+2*m+2*n+13=14*2^n)
    (hback : 2*k+c+2*t+1+c%2=b+d)
    (hpower : d+b/2+3=2^t*(c+3))
    (hbig : 1100*n≤2^n) :
    7*2^n<2*k+8 ∧ 2*k+8<14*2^n := by
  have ht : 1≤t := by
    by_cases hz : t=0
    · subst t; simp at hpower; omega
    · omega
  constructor
  · by_cases ht1 : t=1
    · subst t
      simp at hpower
      have hpow : (2:Nat)^(n-K+2) ≤ 2^(n-m) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.pow_add] at hpow
      simp at hpow
      omega
    · have hpow : (4:Nat)≤2^t := by
        have hh := Nat.pow_le_pow_right (show 0<(2:Nat) by decide) (show 2≤t by omega)
        simpa using hh
      have hcBound : 4*(c+3)≤d+b/2+3 := by
        rw [hpower]
        exact Nat.mul_le_mul_right (c+3) hpow
      omega
  · omega

#print axioms scaled_left_strict
#print axioms even_gap
end BB6.Agent45CarryWide
