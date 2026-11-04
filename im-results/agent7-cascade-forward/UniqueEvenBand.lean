import UniformRootGate

namespace CascadeUniformFatal
open CascadeResetInverse CascadeManyShield

/-- Dyadic even-return image bands have disjoint scales; hence the scale
    exponent of any genuine even first-reset parent is determined by u. -/
theorem even_band_scale_unique (u k j : Nat)
    (hb : 6*2^k-1 ≤ u ∧ u ≤ 8*2^k-3)
    (hj : 6*2^j-1 ≤ u ∧ u ≤ 8*2^j-3) : k=j := by
  by_cases heq : k=j
  · exact heq
  by_cases hlt : k<j
  · have hpow : 2^(k+1) ≤ 2^j :=
      Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega)
    have he : 2^(k+1)=2*2^k := by rw [Nat.pow_succ]; omega
    rw [he] at hpow
    omega
  · have hpow : 2^(j+1) ≤ 2^k :=
      Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega)
    have he : 2^(j+1)=2*2^j := by rw [Nat.pow_succ]; omega
    rw [he] at hpow
    omega

/-- If a reset target belongs to a given even-return dyadic image band
    and has residue different from 2 mod3, any genuine first-reset parent
    is its unique even predecessor, determined by the band's scale. -/
theorem any_parent_equals_even
    (u k h q : Nat)
    (hb : 6*2^k-1 ≤ u ∧ u ≤ 8*2^k-3)
    (heq : 2*u = 8*2^k+h+k)
    (hmod : u%3 ≠ 2)
    (hq : ResetParent q u) : q=h := by
  rcases hq with ⟨j,hj,heqj⟩ | ⟨j,t,d,hd,hj,hout,heqj⟩
  · have he : j=k := even_band_scale_unique u j k hj hb
    rw [he] at heqj
    omega
  · have he : 3^(t+1) = 3*3^t := by
      rw [Nat.pow_succ]
      omega
    rw [he] at hout
    have hz : 2*u+5=3*(3^t*d) := by
      simpa only [Nat.mul_assoc] using hout
    have hm : u%3=2 := by omega
    exact False.elim (hmod hm)

#print axioms even_band_scale_unique
#print axioms any_parent_equals_even
end CascadeUniformFatal
