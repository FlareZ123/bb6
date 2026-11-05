import Lean
namespace BB6.Agent9Budget

/-- An arbitrary 2-adic modulus obstructs inverse depths beyond K. -/
theorem depth_le_of_dyadic_shadow
    (K t s z c : Nat)
    (hmod : 2^(K+1) ∣ s+2*z)
    (hpower : s=2^t*(c+3))
    (hnodiv : ¬2^K ∣ z) : t≤K := by
  by_cases ht : t≤K
  · exact ht
  have hdiv : 2^(K+1) ∣ 2^t := Nat.pow_dvd_pow 2 (by omega)
  have hs : 2^(K+1) ∣ s := by
    rw [hpower]
    obtain ⟨v,hv⟩ := hdiv
    refine ⟨v*(c+3), ?_⟩
    rw [hv]
    simp only [Nat.mul_assoc]
  have h2z : 2^(K+1) ∣ 2*z := by
    have hdiff := Nat.dvd_sub hmod hs
    have hh : s+2*z-s=2*z := by omega
    simpa only [hh] using hdiff
  obtain ⟨v,hv⟩ := h2z
  have hpow : 2^(K+1)=2*2^K := by
    rw [Nat.pow_succ]
    omega
  have hv2 : 2*z = 2*(2^K*v) := by
    rw [hpow] at hv
    simpa only [Nat.mul_assoc] using hv
  have hz : z = 2^K*v :=
    Nat.mul_left_cancel (by decide : 0 < (2:Nat)) hv2
  exact False.elim (hnodiv ⟨v,hz⟩)

#print axioms depth_le_of_dyadic_shadow
end BB6.Agent9Budget
