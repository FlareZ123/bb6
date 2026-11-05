import CDyadicImmediateHalts
import Lean.Elab.Tactic.Omega

namespace BB6CDyadicMod6

/-- The blank class modulo 3*2^e always has a synthetic immediate stop. -/
theorem blank_mod_three_times_power_two_synthetic_stop (e : Nat) :
    ∃ K : Nat, K % (3*(2^e)) = 1 % (3*(2^e)) ∧
      BB6.Agent46.secNext (5,K) = none := by
  obtain ⟨K,hmod2,hhalt⟩ := BB6CDyadicBarrier.blank_class_has_synthetic_halt e
  have hmod3 : K%3=1 :=
    BB6.Agent1Unified.source_positive_stopping_right_mod3 5 K (by decide) hhalt
  have hk : 1 ≤ K := by omega
  have h3 : 3 ∣ K-1 := by
    have h := Nat.mod_add_div K 3
    rw [hmod3] at h
    have he : K-1 = 3*(K/3) := by omega
    rw [he]
    exact Nat.dvd_mul_right _ _
  have h2 : 2^e ∣ K-1 := by
    cases e with
    | zero => simp
    | succ e =>
        have hh : 1 < 2^(e+1) := Nat.one_lt_two_pow (by omega)
        have hmod1 : 1 % (2^(e+1))=1 := Nat.mod_eq_of_lt hh
        have ht := Nat.mod_add_div K (2^(e+1))
        rw [hmod1] at hmod2
        rw [hmod2] at ht
        have he : K-1 = 2^(e+1)*(K/(2^(e+1))) := by omega
        rw [he]
        exact Nat.dvd_mul_right _ _
  have hcp : Nat.Coprime 3 (2^e) :=
    (show Nat.Coprime 3 2 by decide).pow_right e
  have hd : 3*(2^e) ∣ K-1 := hcp.mul_dvd_of_dvd_of_dvd h3 h2
  have he : K=1+(K-1) := by omega
  refine ⟨K,?_,hhalt⟩
  rw [he,Nat.add_mod,Nat.mod_eq_zero_of_dvd hd]
  simp

#print axioms blank_mod_three_times_power_two_synthetic_stop
end BB6CDyadicMod6
