import CapSignedRoots

namespace CapSieve

/-- The first positive coordinate in its same-band 3-multiplication ray. -/
def CanonQ (k q : Nat) : Prop :=
  PosQ k q ∧ (q%3≠0 ∨ q<3*(k+6))

theorem positive_next_phase {k q : Nat} (h : PosQ k q) :
    positiveNext k q%3=2^(k+1)%3 := by
  have hp : 0<q := by have := h.1; omega
  have he := positive_next_equation hp h.2.1
  have hd : positiveProduct k q%3=0 := by
    unfold positiveProduct
    rw [Nat.pow_succ,show 3^(positiveCount k q)*3*q=3*(3^(positiveCount k q)*q) by ac_rfl]
    omega
  rw [Nat.pow_succ]
  unfold P at he
  omega

theorem negative_event_canonical {k w j q : Nat} (hv : CapNegative.Valid k w)
    (he : (CapNegative.event k w).2=some (j,q)) :
    CanonQ j q := by
  have hpos := (negative_event_return hv he).2
  have h := CapNegative.stop_spec hv
  unfold CapNegative.event at he
  dsimp at h he
  generalize CapNegative.stopCount k w = n at *
  generalize k+n = b at *
  generalize 3^n*w = v at *
  have hb := h.1.2.1
  refine ⟨hpos,Or.inr ?_⟩
  by_cases ht : v=2*b+3
  · simp [ht] at he
  · rw [if_neg ht] at he
    by_cases hs : v=2*b+7
    · rw [if_pos hs] at he
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
      omega
    · rw [if_neg hs] at he
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
      omega

/-- Every positive return produced by the signed macro is canonical. -/
theorem signed_event_canonical {k q j v : Nat} (hv : ValidQ k q)
    (he : (signedEvent k q).2=some (j,v)) : CanonQ j v := by
  have hpos := (signed_event_return hv he).2
  unfold signedEvent at he
  by_cases hp : q≤2*P k-2
  · rw [if_pos hp] at he
    dsimp at he
    have hq : PosQ k q := ⟨hv.1,hp,hv.2.2⟩
    by_cases hpass : k+7≤positiveNext k q
    · rw [if_pos hpass] at he
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
      refine ⟨hpos,Or.inl ?_⟩
      rw [positive_next_phase hq]
      rcases two_unit_phase (k+1) with h|h <;> omega
    · rw [if_neg hpass] at he
      exact negative_event_canonical (entry_weight hq (by omega)).1 he
  · rw [if_neg hp] at he
    exact negative_event_canonical (weight_valid hv (by omega)) he

theorem canon_root_two : CanonQ 0 6 := by unfold CanonQ PosQ P; decide
theorem canon_root_three : CanonQ 0 8 := by unfold CanonQ PosQ P; decide
theorem canon_root_one_after_special : CanonQ 1 15 := by unfold CanonQ PosQ P; decide

/-- Two canonical entries cannot lie on the same multiplication ray. -/
theorem canonical_ray_unique {k q v a b : Nat}
    (hq : CanonQ k q) (hv : CanonQ k v)
    (he : 3^a*q=3^b*v) : q=v := by
  have hlt : ∀ {x y i j : Nat}, CanonQ k x → CanonQ k y →
      i<j → 3^i*x=3^j*y → False := by
    intro x y i j hx hy hij heq
    have hd : i+(j-i)=j := by omega
    have hprod : 3^i*x=3^i*(3^(j-i)*y) := by
      rw [←Nat.mul_assoc,←Nat.pow_add,hd]
      exact heq
    have hx' := Nat.mul_left_cancel (Nat.pow_pos (by decide : 0<3)) hprod
    have hdiv : x%3=0 := by
      rw [hx',show j-i=(j-i-1)+1 by omega,Nat.pow_succ,
        show 3^(j-i-1)*3*y=3*(3^(j-i-1)*y) by ac_rfl]
      omega
    have hp : 3≤3^(j-i) := by
      simpa using Nat.pow_le_pow_right (by decide : 0<3) (show 1≤j-i by omega)
    have hmul := Nat.mul_le_mul_right y hp
    have hylo := hy.1.1
    have hcan := hx.2
    omega
  by_cases hab : a=b
  · subst b
    exact Nat.mul_left_cancel (Nat.pow_pos (by decide : 0<3)) he
  · rcases Nat.lt_or_gt_of_ne hab with h|h
    · exact False.elim (hlt hq hv h he)
    · exact False.elim (hlt hv hq h he.symm)

theorem canonical_positive_next_inj {k q v : Nat}
    (hq : CanonQ k q) (hv : CanonQ k v)
    (he : positiveNext k q=positiveNext k v) : q=v := by
  have hqeq := positive_next_equation (show 0<q by have := hq.1.1; omega) hq.1.2.1
  have hveq := positive_next_equation (show 0<v by have := hv.1.1; omega) hv.1.2.1
  have hprod : positiveProduct k q=positiveProduct k v := by omega
  exact canonical_ray_unique hq hv hprod

/-- A fixed terminal exponent determines at most one canonical positive entry. -/
theorem canonical_terminal_exponent_inj {k q v n : Nat}
    (hq : CanonQ k q) (hv : CanonQ k v)
    (he : 3^n*(2*positiveNext k q-3)=2*(k+n)+3)
    (hf : 3^n*(2*positiveNext k v-3)=2*(k+n)+3) : q=v := by
  have hqlo := (positive_next_bounds (show 0<q by have := hq.1.1; omega) hq.1.2.1).1
  have hvlo := (positive_next_bounds (show 0<v by have := hv.1.1; omega) hv.1.2.1).1
  have hh := Nat.mul_left_cancel (Nat.pow_pos (by decide : 0<3)) (he.trans hf.symm)
  exact canonical_positive_next_inj hq hv (by omega)

#print axioms signed_event_canonical
#print axioms canonical_ray_unique
#print axioms canonical_positive_next_inj
#print axioms canonical_terminal_exponent_inj
end CapSieve
