import AsymmetricShift
import RotationValuation

namespace NeedleRotation.Asymmetric

/-- 3^q fits in 8 bits per block of 5 powers, with an upward rounding. -/
theorem pow3_bound (q : Nat) : 3^q ≤ 2^(8*((q+4)/5)) := by
  let p := (q+4)/5
  have hq : q≤5*p := by dsimp [p]; omega
  calc
    3^q ≤ 3^(5*p) := Nat.pow_le_pow_right (by decide) hq
    _ = (3^5)^p := Nat.pow_mul _ _ _
    _ ≤ (2^8)^p := Nat.pow_le_pow_left (by decide) _
    _ = 2^(8*p) := (Nat.pow_mul _ _ _).symm

def width (m e H : Nat) : Nat := H+8*((((e+m-1)/m)+4)/5)+2

theorem width_const (m H : Nat) (hm : 0<m) : width m 0 H=H+2 := by
  have hq : (m-1)/m=0 := Nat.div_eq_of_lt (by omega)
  simp [width,hq]

theorem rotated_term_small (m h e H : Nat) (c : Int)
    (hh : h<m) (hc : c.natAbs<2^H)
    (hr : (e+h)%m+width m e H<m) :
    ((rotateTerm m h (c,e)).1*2^(rotateTerm m h (c,e)).2).natAbs < 2^(m-2) := by
  let q := (e+h)/m
  let s := (e+h)%m
  let p := (((e+m-1)/m)+4)/5
  have hq : q≤(e+m-1)/m := Nat.div_le_div_right (by omega)
  have hp : (q+4)/5≤p := Nat.div_le_div_right (by omega)
  have hpow : 3^q≤2^(8*p) :=
    Nat.le_trans (pow3_bound q) (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hp))
  have hpow3 : 0<3^q := Nat.pow_pos (by decide)
  have hprod : c.natAbs*3^q<2^H*2^(8*p) := by
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hc hpow3) (Nat.mul_le_mul_left _ hpow)
  have hexp : H+8*p+s≤m-2 := by
    dsimp [width] at hr
    dsimp [p,s]
    omega
  simp only [rotateTerm,Int.natAbs_mul,Int.natAbs_pow]
  change c.natAbs*3^q*2^s < 2^(m-2)
  calc
    c.natAbs*3^q*2^s < 2^H*2^(8*p)*2^s := Nat.mul_lt_mul_of_pos_right hprod (Nat.two_pow_pos _)
    _ = 2^(H+8*p+s) := by rw [←Nat.pow_add,←Nat.pow_add]
    _ ≤ 2^(m-2) := Nat.pow_le_pow_right (by decide) hexp

/-- A signed three-term congruence has the constant-term divisibility consequence
    once the SUM of its separate coefficient widths fits. -/
theorem constant_dvd_of_width_sum
    (m a e f H₁ H₂ H₃ : Nat) (c d C : Int)
    (hae : a≤e) (haf : a≤f)
    (hc : c.natAbs<2^H₁) (hd : d.natAbs<2^H₂) (hC : C.natAbs<2^H₃)
    (hsize : width m e H₁+width m f H₂+width m 0 H₃<m)
    (hdiv : denominator m ∣ value [(c,e),(d,f),(C,0)]) :
    (3:Int)^(a/m) ∣ C := by
  obtain ⟨h,hh,hr₁,hr₂,hr₃⟩ := exists_weighted_shift m e f _ _ _ hsize
  have h₁ := rotated_term_small m h e H₁ c hh hc hr₁
  have h₂ := rotated_term_small m h f H₂ d hh hd hr₂
  have h₃ := rotated_term_small m h 0 H₃ C hh hC (by simpa [Nat.mod_eq_of_lt hh] using hr₃)
  have hsmall : (value (rotate m h [(c,e),(d,f),(C,0)])).natAbs < (denominator m).natAbs := by
    simp only [rotate,List.map_cons,List.map_nil,value,Int.add_zero]
    have ht := Int.natAbs_add_le
      ((rotateTerm m h (c,e)).1*2^(rotateTerm m h (c,e)).2)
      ((rotateTerm m h (d,f)).1*2^(rotateTerm m h (d,f)).2+
       (rotateTerm m h (C,0)).1*2^(rotateTerm m h (C,0)).2)
    have hu := Int.natAbs_add_le
      ((rotateTerm m h (d,f)).1*2^(rotateTerm m h (d,f)).2)
      ((rotateTerm m h (C,0)).1*2^(rotateTerm m h (C,0)).2)
    have hm : 2≤m := by simp [width] at hsize; omega
    have hpow : 2^m=4*2^(m-2) := by
      change 2^m=2^2*2^(m-2)
      rw [←Nat.pow_add,show 2+(m-2)=m by omega]
    have heq : (denominator m).natAbs=2^m+3 := by
      simp [denominator,Int.natAbs_pow,Int.natAbs_add_of_nonneg,Int.pow_nonneg]
    rw [heq,hpow]
    omega
  have hzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (rotated_divisibility m h _ hdiv) hsmall
  have h1 := three_power_dvd_term m h a (c,e) hae
  have h2 := three_power_dvd_term m h a (d,f) haf
  have h12 := Int.dvd_add h1 h2
  simp only [rotate,List.map_cons,List.map_nil,rotateTerm,value,Int.add_zero] at hzero
  simp only [rotateTerm] at h12
  simp [Nat.div_eq_of_lt hh, Nat.mod_eq_of_lt hh] at hzero
  have heq : C*2^h = -((c*(-3)^((e+h)/m))*2^((e+h)%m)+(d*(-3)^((f+h)/m))*2^((f+h)%m)) := by omega
  have hCd : (3:Int)^(a/m) ∣ C*2^h := by
    rw [heq,Int.dvd_neg]
    exact h12
  apply Int.natAbs_dvd_natAbs.mp
  have hNat := Int.natAbs_dvd_natAbs.mpr hCd
  simp only [Int.natAbs_pow,Int.natAbs_mul] at hNat ⊢
  exact (((by decide : (3:Nat).Coprime 2).pow_left (a/m)).pow_right h).dvd_of_dvd_mul_right hNat

#print axioms pow3_bound
#print axioms rotated_term_small
#print axioms constant_dvd_of_width_sum
end NeedleRotation.Asymmetric
