import BMod7Core
namespace BB6.OneDim

theorem five_pow_mod7_period (n : Nat) : (5^(n+6))%7 = (5^n)%7 := by
  rw [Nat.pow_add]
  have h6 : (5^6)%7=1 := by decide
  calc
    (5^n*5^6)%7 = ((5^n)%7*((5^6)%7))%7 := Nat.mul_mod _ _ _
    _ = (5^n)%7 := by rw [h6]; omega

theorem five_pow_mod7_mod6 (n : Nat) : (5^n)%7 = (5^(n%6))%7 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases h : n<6
      · rw [Nat.mod_eq_of_lt h]
      · have heq : n-6+6=n := by omega
        calc
          (5^n)%7 = (5^((n-6)+6))%7 := by rw [heq]
          _ = (5^(n-6))%7 := five_pow_mod7_period (n-6)
          _ = (5^((n-6)%6))%7 := ih (n-6) (by omega)
          _ = (5^(n%6))%7 := by
            have hmod : (n-6)%6=n%6 := by omega
            rw [hmod]

end BB6.OneDim
