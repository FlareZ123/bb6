import Lean
namespace BB6.Shadow

/-- Eight-bit modular obstruction to deep original inverse branches. -/
theorem q29_depth_modular (t s z c : Nat)
 (hmod : 2^9 ∣ s+2*z)
 (hpower : s=2^t*(c+3))
 (hnodiv : ¬256 ∣ z) : t ≤ 8 := by
  by_cases ht:t≤8
  · exact ht
  · have hpow : 2^9 ∣ 2^t := Nat.pow_dvd_pow 2 (by omega)
    have hds : 2^9 ∣ s := by
      rw [hpower]
      obtain ⟨v,hv⟩ := hpow
      refine ⟨v*(c+3), ?_⟩
      rw [hv]
      simp only [Nat.mul_assoc]
    have h2z : 2^9 ∣ 2*z := by
      have hdiff := Nat.dvd_sub hmod hds
      have hh : s+2*z-s=2*z := by omega
      simpa only [hh] using hdiff
    obtain ⟨v,hv⟩ := h2z
    have hz : 256 ∣ z := by
      refine ⟨v, ?_⟩
      have h512 : (2:Nat)^9=512 := by decide
      rw [h512] at hv
      omega
    exact False.elim (hnodiv hz)

#print axioms q29_depth_modular
end BB6.Shadow
