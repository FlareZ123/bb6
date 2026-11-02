import GInverse

namespace BB6.Agent44

/-- The exact inverse branch at a selected recursion depth. Starting index zero
corresponds to the unique high-output predecessor. -/
def invAt (b d : Nat) : Nat → Nat × Nat
  | 0 => (b/4-1, d+b/2)
  | n+1 =>
      let p := invAt b d n
      (p.1 + ((p.2-3)/2)/2 + 1, (p.2-3)/2)

/-- Every authentic GAncestor appears in the deterministic inverse sequence
at its exact nesting depth, with the correct shifted two-adic identity. -/
theorem GAncestor_invAt (b d k c : Nat)
    (h : BB6.P1Reduction.GAncestor b d k c) :
    ∃ n : Nat, invAt b d n = (k,c) ∧
      d+b/2+3 = 2^n*(c+3) := by
  induction h with
  | upper k d =>
    refine ⟨0, ?_, ?_⟩
    · simp only [invAt]
      apply Prod.ext <;> dsimp <;> omega
    · simp; omega
  | nest b d k c h ih =>
    obtain ⟨n,hn,hpow⟩ := ih
    refine ⟨n+1, ?_, ?_⟩
    · simp only [invAt, hn]
      apply Prod.ext <;> dsimp <;> omega
    · calc
        d+b/2+3 = 2^n*((2*c+3)+3) := hpow
        _ = 2^n*(2*(c+3)) := by congr 1
        _ = (2^n*2)*(c+3) := by rw [Nat.mul_assoc]
        _ = 2^(n+1)*(c+3) := by rw [Nat.pow_succ]

/-- A nonzero 2-adic remainder bounds the exact nesting depth. -/
theorem GAncestor_invAt_bounded (b d k c m : Nat)
    (h : BB6.P1Reduction.GAncestor b d k c)
    (hn : (d+b/2+3) % 2^(m+1) ≠ 0) :
    ∃ n : Nat, n ≤ m ∧ invAt b d n = (k,c) := by
  obtain ⟨n,hval,hpow⟩ := GAncestor_invAt b d k c h
  refine ⟨n, ?_, hval⟩
  by_cases hle : n ≤ m
  · exact hle
  · have hm : m+1 ≤ n := by omega
    obtain ⟨z,hz⟩ := Nat.pow_dvd_pow 2 hm
    have hd : 2^(m+1) ∣ d+b/2+3 := by
      rw [hpow, hz]
      exact ⟨z*(c+3), by simp [Nat.mul_assoc]⟩
    exact False.elim (hn (Nat.mod_eq_zero_of_dvd hd))

/-- If an affine coefficient is divisible by modulus, the affine parameter
has no influence on the result's remainder. -/
theorem affine_remainder (A C t D modulus : Nat)
    (hD : D=A*t+C) (hA : A%modulus=0) :
    D%modulus=C%modulus := by
  subst D
  simp [Nat.add_mod, Nat.mul_mod, hA]

/-- Source-linked complete finite inverse enumeration from affine node
coefficients and one divisibility certificate. -/
theorem affine_GAncestor_bounded (b d k c A C t m : Nat)
    (h : BB6.P1Reduction.GAncestor b d k c)
    (hD : d+b/2+3=A*t+C)
    (hA : A%2^(m+1)=0)
    (hC : C%2^(m+1)≠0) :
    ∃ n : Nat, n≤m ∧ invAt b d n=(k,c) := by
  apply GAncestor_invAt_bounded b d k c m h
  rw [affine_remainder A C t (d+b/2+3) (2^(m+1)) hD hA]
  exact hC

#print axioms BB6.Agent44.GAncestor_invAt
#print axioms BB6.Agent44.GAncestor_invAt_bounded
#print axioms BB6.Agent44.affine_GAncestor_bounded
end BB6.Agent44
