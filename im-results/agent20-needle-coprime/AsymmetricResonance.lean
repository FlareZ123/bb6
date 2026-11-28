import AsymmetricRotation

namespace NeedleRotation.Asymmetric

theorem rotated_term_small_at_shift (m h e H : Nat) (c : Int)
    (hh : h<m) (hc : c.natAbs<2^H)
    (hr : (e+h)%m+(H+8*((((e+h)/m)+4)/5)+2)<m) :
    ((rotateTerm m h (c,e)).1*2^(rotateTerm m h (c,e)).2).natAbs < 2^(m-2) := by
  let q := (e+h)/m
  let s := (e+h)%m
  let p := (q+4)/5
  have hpow : 3^q≤2^(8*p) := pow3_bound q
  have hpow3 : 0<3^q := Nat.pow_pos (by decide)
  have hprod : c.natAbs*3^q<2^H*2^(8*p) := by
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hc hpow3) (Nat.mul_le_mul_left _ hpow)
  have hexp : H+8*p+s≤m-2 := by
    dsimp [q,p,s] at *
    omega
  simp only [rotateTerm,Int.natAbs_mul,Int.natAbs_pow]
  change c.natAbs*3^q*2^s < 2^(m-2)
  calc
    c.natAbs*3^q*2^s < 2^H*2^(8*p)*2^s := Nat.mul_lt_mul_of_pos_right hprod (Nat.two_pow_pos _)
    _ = 2^(H+8*p+s) := by rw [←Nat.pow_add,←Nat.pow_add]
    _ ≤ 2^(m-2) := Nat.pow_le_pow_right (by decide) hexp

theorem rotation_zero_of_three_small (m h e f : Nat) (c d C : Int)
    (hm : 2≤m)
    (h₁ : ((rotateTerm m h (c,e)).1*2^(rotateTerm m h (c,e)).2).natAbs < 2^(m-2))
    (h₂ : ((rotateTerm m h (d,f)).1*2^(rotateTerm m h (d,f)).2).natAbs < 2^(m-2))
    (h₃ : ((rotateTerm m h (C,0)).1*2^(rotateTerm m h (C,0)).2).natAbs < 2^(m-2))
    (hdiv : denominator m ∣ value [(c,e),(d,f),(C,0)]) :
    value (rotate m h [(c,e),(d,f),(C,0)])=0 := by
  have hsmall : (value (rotate m h [(c,e),(d,f),(C,0)])).natAbs < (denominator m).natAbs := by
    simp only [rotate,List.map_cons,List.map_nil,value,Int.add_zero]
    have ht := Int.natAbs_add_le
      ((rotateTerm m h (c,e)).1*2^(rotateTerm m h (c,e)).2)
      ((rotateTerm m h (d,f)).1*2^(rotateTerm m h (d,f)).2+
       (rotateTerm m h (C,0)).1*2^(rotateTerm m h (C,0)).2)
    have hu := Int.natAbs_add_le
      ((rotateTerm m h (d,f)).1*2^(rotateTerm m h (d,f)).2)
      ((rotateTerm m h (C,0)).1*2^(rotateTerm m h (C,0)).2)
    have hpow : 2^m=4*2^(m-2) := by
      change 2^m=2^2*2^(m-2)
      rw [←Nat.pow_add,show 2+(m-2)=m by omega]
    have heq : (denominator m).natAbs=2^m+3 := by
      simp [denominator,Int.natAbs_pow,Int.natAbs_add_of_nonneg,Int.pow_nonneg]
    rw [heq,hpow]
    omega
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (rotated_divisibility m h _ hdiv) hsmall

/-- Exact coefficient-specific rotation excludes nonresonant divisibility. -/
theorem nonresonant_of_zero (m h e f x y z : Nat) (u v w : Int)
    (hm : 0<m) (hu : u%2=1) (hv : v%2=1) (hw : w%2=1)
    (hxy : (e+x)%m ≠ (f+y)%m)
    (hxz : (e+x)%m ≠ z%m)
    (hyz : (f+y)%m ≠ z%m) :
    value (rotate m h [(u*2^x,e),(v*2^y,f),(w*2^z,0)]) ≠ 0 := by
  intro hzero
  have hnon := three_odd_distinct (u*(-3)^((e+h)/m)) (v*(-3)^((f+h)/m)) (w*(-3)^((0+h)/m))
    ((e+h)%m+x) ((f+h)%m+y) ((0+h)%m+z)
    (odd_mul_neg_three_pow _ _ hu) (odd_mul_neg_three_pow _ _ hv) (odd_mul_neg_three_pow _ _ hw)
    (adjusted_distinct m h e f x y hm hxy)
    (adjusted_distinct m h e 0 x z hm (by simpa using hxz))
    (adjusted_distinct m h f 0 y z hm (by simpa using hyz))
  apply hnon
  simp only [rotate,List.map_cons,List.map_nil,rotateTerm,value,Int.add_zero] at hzero
  simp only [Int.pow_add]
  grind

/-- All signed three-term congruences: only small denominators or a collision
    of two binary-valuation-adjusted exponent residues are possible. -/
theorem asymmetric_resonance_or_small
    (m e f x y z H₁ H₂ H₃ : Nat) (u v w : Int)
    (hu : u%2=1) (hv : v%2=1) (hw : w%2=1)
    (hc : (u*2^x).natAbs<2^H₁) (hd : (v*2^y).natAbs<2^H₂) (hC : (w*2^z).natAbs<2^H₃)
    (hdiv : denominator m ∣ value [(u*2^x,e),(v*2^y,f),(w*2^z,0)]) :
    m≤width m e H₁+width m f H₂+width m 0 H₃ ∨
    (e+x)%m=(f+y)%m ∨ (e+x)%m=z%m ∨ (f+y)%m=z%m := by
  by_cases hsize : width m e H₁+width m f H₂+width m 0 H₃<m
  · right
    by_cases hxy : (e+x)%m=(f+y)%m
    · exact Or.inl hxy
    by_cases hxz : (e+x)%m=z%m
    · exact Or.inr (Or.inl hxz)
    by_cases hyz : (f+y)%m=z%m
    · exact Or.inr (Or.inr hyz)
    exfalso
    obtain ⟨h,hh,hr₁,hr₂,hr₃⟩ := exists_weighted_shift m e f _ _ _ hsize
    have h₁ := rotated_term_small m h e H₁ (u*2^x) hh hc hr₁
    have h₂ := rotated_term_small m h f H₂ (v*2^y) hh hd hr₂
    have h₃ := rotated_term_small m h 0 H₃ (w*2^z) hh hC (by simpa [Nat.mod_eq_of_lt hh] using hr₃)
    have hm : 2≤m := by simp [width] at hsize; omega
    exact nonresonant_of_zero m h e f x y z u v w (by omega) hu hv hw hxy hxz hyz
      (rotation_zero_of_three_small m h e f _ _ _ hm h₁ h₂ h₃ hdiv)
  · exact Or.inl (by omega)

#print axioms rotated_term_small_at_shift
#print axioms rotation_zero_of_three_small
#print axioms asymmetric_resonance_or_small
end NeedleRotation.Asymmetric
