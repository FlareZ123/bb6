import P1CriticalValuation

namespace BB6.Agent47P1

/-- All critical hubs from even exponents at least 4 lie in the positive,
multiple-of-four G-output sector of the genuine P1 map. -/
theorem critical_even_hub_form (n : Nat) (hn : 4 ≤ n)
    (he : n%2=0) :
    8 ≤ 14*2^n-2*n-16 ∧
    (14*2^n-2*n-16)%4=0 := by
  have hpow : n+2 < 2^n := n_plus_two_lt_pow n hn
  have hd : 4 ∣ (2:Nat)^n := by
    simpa using (Nat.pow_dvd_pow 2 (show 2 ≤ n by omega))
  have hmod : (2^n)%4=0 := Nat.mod_eq_zero_of_dvd hd
  constructor <;> omega

/-- The target-counter hypotheses for Agent50's raw-blank reset gateway. -/
theorem critical_even_target_form (n : Nat) (hn : 4 ≤ n)
    (he : n%2=0) :
    10 ≤ 14*2^n-2*n-10 ∧
    (14*2^n-2*n-10)%4=2 := by
  have hpow : n+2 < 2^n := n_plus_two_lt_pow n hn
  have hd : 4 ∣ (2:Nat)^n := by
    simpa using (Nat.pow_dvd_pow 2 (show 2 ≤ n by omega))
  have hmod : (2^n)%4=0 := Nat.mod_eq_zero_of_dvd hd
  constructor <;> omega

#print axioms critical_even_hub_form
#print axioms critical_even_target_form
end BB6.Agent47P1
