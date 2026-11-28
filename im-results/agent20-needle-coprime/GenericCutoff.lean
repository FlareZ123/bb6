import AsymmetricResonance
import CancellationNarrow

namespace NeedleRotation.Asymmetric

/-- Explicit quadratic bound implied by the separate forbidden widths. -/
theorem width_quadratic (m e f H₁ H₂ H₃ : Nat) (hm : 0<m)
    (hsmall : m≤width m e H₁+width m f H₂+width m 0 H₃) :
    5*(m*m)≤5*(H₁+H₂+H₃+22)*m+8*(e+f) := by
  have h1 := width_scaled m e H₁
  have h2 := width_scaled m f H₂
  have h3 := width_const m H₃ hm
  have h := Nat.mul_le_mul_left 5 (Nat.mul_le_mul_right m hsmall)
  rw [h3] at h
  rw [show (width m e H₁+width m f H₂+(H₃+2))*m=width m e H₁*m+width m f H₂*m+(H₃+2)*m by grind] at h
  rw [Nat.mul_add,Nat.mul_add] at h
  have h4 : 5*(H₁+H₂+H₃+22)*m = 5*(H₁+10)*m+5*(H₂+10)*m+5*((H₃+2)*m) := by grind
  rw [h4]
  omega

theorem residue_dvd_sub (m e f : Nat) (hle : f≤e)
    (h : e%m=f%m) : m∣e-f := by
  refine ⟨e/m-f/m,?_⟩
  have h1 := Nat.div_add_mod e m
  have h2 := Nat.div_add_mod f m
  have hle' := Nat.div_le_div_right hle (c:=m)
  have hmul := Nat.mul_sub_left_distrib m (e/m) (f/m)
  omega

/-- A single quadratic bound and three divisors suffice for every affine reverse
    node with even leading coefficient and odd correction. -/
theorem affine_even_quadratic_or_divisors (m E a x H₁ H₂ H₃ : Nat) (N C : Int)
    (hm : 0<m) (hx : 0<x) (ha : a≤E) (hodd : C%2=1)
    (hc : ((2:Int)^x).natAbs<2^H₁)
    (hd : (C-(2:Int)^x*N).natAbs<2^H₂)
    (hC : (3*C).natAbs<2^H₃)
    (hdiv : denominator m∣value [((2:Int)^x,E),(C-(2:Int)^x*N,a),(3*C,0)]) :
    5*(m*m)≤5*(H₁+H₂+H₃+22)*m+8*(E+a) ∨
      m∣E+x-a ∨ m∣E+x ∨ m∣a := by
  have hpow : (2:Int)^x%2=0 := by
    rw [show x=x-1+1 by omega,Int.pow_succ,Int.mul_emod]
    simp
  have hv : (C-(2:Int)^x*N)%2=1 := by
    rw [Int.sub_emod,Int.mul_emod,hpow,hodd]
    simp
  have hw : (3*C)%2=1 := by rw [Int.mul_emod,hodd]; decide
  have h := asymmetric_resonance_or_small m E a x 0 0 H₁ H₂ H₃
    1 (C-(2:Int)^x*N) (3*C) (by decide) hv hw
    (by simpa using hc) (by simpa using hd) (by simpa using hC) (by simpa using hdiv)
  rcases h with h|h|h|h
  · exact Or.inl (width_quadratic m E a H₁ H₂ H₃ hm h)
  · exact Or.inr (Or.inl (residue_dvd_sub m (E+x) a (by omega) (by simpa using h)))
  · exact Or.inr (Or.inr (Or.inl (Nat.dvd_of_mod_eq_zero (by simpa using h))))
  · exact Or.inr (Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero (by simpa using h))))

#print axioms width_quadratic
#print axioms residue_dvd_sub
#print axioms affine_even_quadratic_or_divisors
end NeedleRotation.Asymmetric
