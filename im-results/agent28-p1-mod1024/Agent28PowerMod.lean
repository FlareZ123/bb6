import GInverse

namespace BB6.Agent28
open BB6.P1Reduction

/-- Any GAncestor whose right input plus three is divisible by m also has its
output mass d+b/2+3 divisible by m. -/
theorem ancestor_not_mod (b d k c m : Nat)
    (h : GAncestor b d k c)
    (hc : (c+3)%m=0) (hs : (d+b/2+3)%m≠0) : False := by
  obtain ⟨t,ht⟩ := GAncestor_power b d k c h
  have hh : (2^t*(c+3))%m=0 := by
    rw [Nat.mul_mod, hc]
    simp
  rw [← ht] at hh
  exact hs hh

/-- A power of two with residue 2^v modulo 2^(v+1) has exponent v. -/
theorem binary_power_mod (v e : Nat)
    (h : (2^e)%(2^(v+1)) = 2^v) : e=v := by
  by_cases he : e<v
  · have hp : (2:Nat)^e < 2^(v+1) :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    have hm : (2:Nat)^e % 2^(v+1) = 2^e := Nat.mod_eq_of_lt hp
    have hsmall : (2:Nat)^e < 2^v :=
      Nat.pow_lt_pow_right (by decide) he
    omega
  · by_cases he2 : v<e
    · have hd : (2:Nat)^(v+1) ∣ 2^e :=
        Nat.pow_dvd_pow 2 (by omega)
      have hm : (2:Nat)^e % 2^(v+1)=0 :=
        Nat.mod_eq_zero_of_dvd hd
      omega
    · omega

/-- An exceptional input 1 would force d+b/2+3 to be a pure power of two. -/
theorem ancestor_one_power (b d k : Nat)
    (h:GAncestor b d k 1) :
    ∃ e:Nat, d+b/2+3 = 2^e := by
  obtain ⟨t,ht⟩ := GAncestor_power b d k 1 h
  refine ⟨t+2, ?_⟩
  simpa [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using ht

/-- Uniform congruence-and-size exclusion of the exceptional G input 1. -/
theorem ancestor_one_exclusion (b d n:Nat)
    (hmod : (d+b/2+3) % (2^(n+1)) = 2^n)
    (hlarge : 2^n < d+b/2+3) :
    ∀ k, ¬GAncestor b d k 1 := by
  intro k h
  obtain ⟨e, he⟩ := ancestor_one_power b d k h
  have hm : (2^e)%(2^(n+1))=2^n := by
    rw [←he]
    exact hmod
  have heq : e=n := binary_power_mod n e hm
  rw [heq] at he
  omega

end BB6.Agent28
