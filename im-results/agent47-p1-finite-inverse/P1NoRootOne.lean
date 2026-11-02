import P1FiniteInverse

namespace BB6.Agent47P1
open BB6.P1Reduction

private theorem linear_pow_lower (n : Nat) : n+2 < 3*2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

private theorem not_between_consecutive_quad_powers (n t x : Nat)
    (hl : 4*2^n < x) (hu : x < 8*2^n) (he : x=4*2^t) : False := by
  have hlo : 2^n < 2^t := by omega
  have hi : 2^t < 2^(n+1) := by
    have heq : 8*2^n=4*2^(n+1) := by rw [Nat.pow_succ]; omega
    rw [heq] at hu
    omega
  have hnt : n<t := (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hlo
  have htn : t<n+1 := (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hi
  omega

/-- Every n>=4 critical hub has NO exceptional c=1 source G inverse.
    This applies uniformly across all index residues (even and odd);
    it is a structural obstruction, not proof that the hub is unreachable. -/
theorem critical_hub_no_one (n k : Nat) (hn : 4 ≤ n) :
    ¬ GAncestor (14*2^n-2*n-16) 3 k 1 := by
  intro ha
  have hlin : n+2 < 3*2^n := linear_pow_lower n
  have hp : 4 ≤ 2^n := by
    have h := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show 2 ≤ n by omega)
    simpa using h
  have hbval : (14*2^n-2*n-16)/2 = 7*2^n-n-8 := by omega
  obtain ⟨t,ht⟩ := GAncestor_power _ _ _ _ ha
  have hS : 3 + (14*2^n-2*n-16)/2+3 = 7*2^n-n-2 := by
    rw [hbval]
    omega
  have he : 7*2^n-n-2 = 4*2^t := by
    simpa only [show 1+3=4 by omega, Nat.mul_comm] using (hS.symm.trans ht)
  have hl : 4*2^n < 7*2^n-n-2 := by omega
  have hu : 7*2^n-n-2 < 8*2^n := by omega
  exact not_between_consecutive_quad_powers n t _ hl hu he

#print axioms critical_hub_no_one
end BB6.Agent47P1
