import P1InverseLog

namespace BB6.Agent27Finite
open BB6.Agent47P1 BB6.P1Reduction

private theorem power_two_inj (i j : Nat)
    (h : (2:Nat)^i = 2^j) : i=j := by
  by_cases hij : i<j
  · have hp := Nat.pow_lt_pow_right (show 1<(2:Nat) by decide) hij
    omega
  · by_cases hji : j<i
    · have hp := Nat.pow_lt_pow_right (show 1<(2:Nat) by decide) hji
      omega
    · omega

/-- Two authentic source G inverse edges with the same child have
identical parent and identical depth. This also handles the exceptional
right-five child (c=1). No bounded search is involved. -/
theorem unique_inverse_edge (b d t k c b' d' t' k' c' : Nat)
    (h : inverseAt b d t = some (k,c))
    (h' : inverseAt b' d' t' = some (k',c'))
    (hk : 2≤k) (hk' : 2≤k')
    (hchild : (2*k-4,c+4) = (2*k'-4,c'+4)) :
    b=b' ∧ d=d' ∧ t=t' := by
  obtain ⟨hbchild,hdchild⟩ := Prod.mk.inj hchild
  have hkeq : k=k' := by omega
  have hceq : c=c' := by omega
  have hs : G k c = (b,d) :=
    GAncestor_sound b d k c (inverseAt_sound b d t k c h)
  have hs' : G k' c' = (b',d') :=
    GAncestor_sound b' d' k' c' (inverseAt_sound b' d' t' k' c' h')
  rw [← hkeq, ← hceq] at hs'
  have heq : (b,d)=(b',d') := hs.symm.trans hs'
  obtain ⟨hbeq,hdeq⟩ := Prod.mk.inj heq
  subst b'
  subst d'
  have hp := inverseAt_power b d t k c h
  have hp' := inverseAt_power b d t' k' c' h'
  rw [← hceq] at hp'
  have hpow : (2:Nat)^t=2^t' :=
    Nat.eq_of_mul_eq_mul_right (by omega) (hp.symm.trans hp')
  exact ⟨rfl,rfl,power_two_inj t t' hpow⟩

#print axioms unique_inverse_edge
end BB6.Agent27Finite
